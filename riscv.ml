open Core_kernel.Std
open Bap.Std
open Or_error.Monad_infix

module Insn = Disasm_expert.Basic.Insn

module Riscv = struct
  (** Defines the register map *)
  module CPU = struct
    let mem = Var.create "mem" @@ mem32_t `r8
    let reg name = Var.create name reg32_t
    let regs pref = Array.init ~f:(fun i -> reg @@ sprintf "%s%d" pref i)
    let zero = reg "zero"
    let r = regs "r" 31

    (* Core registers are aliased in RISC-V *)
    let r0 = zero
    let r1 = ra
    let r2 = sp
    let r3 = gp
    let r4 = tp
    let r8 = fp

    let gprs = Array.concat [
        r;
      [|zero; gp; tp; sp; fp; ra|] ;
    ]
    (* TODO: there are some aliases for those registers - how to solve that? *)

    let gpr = Array.to_list gprs |> Var.Set.of_list

    let reg_of_name name =
      let name = String.lowercase name in
      Array.find gprs ~f:(fun reg ->
      Var.name reg = name)

    (* the problem is that RISC-V doesn't have flags at all,
       but we can just pretend that they are. They will not
       be used.
       Seems that a drawback of some BAP architecture...
       *)
    let flag n = Var.create n bool_t
    let zf = flag "zf"
    let cf = flag "cf"
    let vf = flag "vf"
    let nf = flag "nf"
    let never _ = false
    let is_reg = Set.mem gpr
    let is_flag = never
    let is_zf = never
    let is_cf = never
    let is_vf = never
    let is_nf = never
    let is_sp v = Var.same v sp
    let is_bp v = Var.same v fp
    let is_mem v = Var.same v mem
  end

  (** simplify an expression by applying constant folding *)
  let simpl = Bil.fixpoint Bil.fold_consts

  (** [reg op] is [Ok reg] if operand is a register with the same
      name as reg *)
  let reg = function
    | Op.Imm _ | Op.Fmm _ -> Or_error.errorf "expected register"
    | Op.Reg reg ->
      let name = Reg.name reg in
      match CPU.reg_of_name name with
      | None -> invalid_argf "unknown register %s" name ()
      | Some reg -> Ok reg


  (** [r_type f d s t] uses lifter [f] for an r-type instruction with
      arguments [d], [s], and [t]. TODO: add shift, and the rest.  *)
  let r_type f d s t = match reg d, reg s, reg t with
    | Ok d, Ok s, Ok t -> Ok (simpl (f d s t))
    | e1,e2,e3 -> Or_error.errorf "invalid instruction"

  (** [!$reg] lifts [reg] into a Bil expression, substitution a zero
      register with zero value (a smart version of [Bil.Var]. *)
  let (!$) reg =
    if Var.equal reg CPU.zero
    then Bil.int (Word.zero 32)
    else Bil.var reg


  (** {2 Instruction semantics}  *)

  let addi r0 r1 r2 = Bil.[
      r0 := !$r1 + !$r2;
    ]
  let add r0 r1 r2 = Bil.[
      r0 := !$r1 + !$r2;
    ]
  let sub r0 r1 r2 = Bil.[
      r0 := !$r1 - !$r2;
    ]
  let lui r0 imm = Bil.[
      r0 := !$imm lsl 12;
    ]
  let auipc r0 imm = Bil.[
      r0 := pc + (imm lsl 12);
    ]
  let _and r0 r1 r2 = Bil.[
      r0 := !$r1 land !$r2;
    ]
  let andi r0 r1 imm = Bil.[
      r0 := !$r1 land imm;
    ]
  let sll r0 r1 r2 = Bil.[
      r0 := !$r1 lsl !$r2;
    ]
  let slli r0 r1 imm = Bil.[
      r0 := !$r1 lsl imm;
    ]
  let srl r0 r1 r2 = Bil.[
      r0 := !$r1 lsr !$r2;
    ]
  let srli r0 r1 imm = Bil.[
      r0 := !$r1 lsr imm;
    ]
  let _or r0 r1 r2 = Bil.[
      r0 := !$r1 lor !$r2;
    ]
  let ori r0 r1 imm = Bil.[
      r0 := !$r1 lor imm;
    ]
  (** [lift mem insn] dispatches instructions to corresponding lifters. *)
  let lift_arith mem insn = match Insn.name insn, Insn.ops insn with
    | "ADD", [|r0;r1|] -> r_type add r0 r1
    | "ADDI", [|r0;r1;r2|] -> r_type addi r0 r1 r2
    | "SLT", [|r0;r1;r2|] -> r_type slt r0 r1 r2
    | "SLTI", [|r0;r1|] -> r_type slti r0 r1
    | "SLTU", [|r0;r1;r2|] -> r_type s_sltu r0 r1 r2
    | "SLTIU", [|r0;r1|] -> r_type sltiu r0 r1
    | "SLL", [|r0;r1;r2|] -> r_type sll r0 r1 r2
    | "SLLI", [|r0;r1|] -> r_type slli r0 r1
    | "SRL", [|r0;r1|] -> r_type srl r0 r2
    | "SRLI", [|r0;r1|] -> r_type srli r0 r1
    | "SRA", [|r0;r1;r2|] -> r_type sra r0 r1 r2
    | "SRAI", [|r0;r1|] -> r_type srai r0 r1
    | "AND", [|r0;r1|] -> r_type _and r0 r1
    | "ANDI", [|r0;r1|] -> r_type andi r0 r1
    | "OR", [|r0;r1|] -> r_type _or r0 r1
    | "ORI", [|r0;r1|] -> r_type ori r0 r1
    | "SUB", [|r0;r1;r2|] -> r_type sub r0 r1 r2
    | "XOR", [|r0;r1|] -> r_type xor r0 r1
    | "XORI", [|r0;r1;imm|] -> r_type xori r0 r1 imm
    | "LUI", [|r0;imm|] -> r_type lui r0 imm
    | "AUIPC", [|r0;imm|] -> r_type auipc r0 imm
    | _ -> Ok [Bil.special (Insn.asm insn)]

  let lift_mem mem insn = match Insn.name insn, Insn.ops insn with
    | "LW", [|r0;r1;offset|] -> r_type load word r0 r1 offset
    | "LH", [|r0;r1;offset|] -> r_type load halfword r0 r1 offset
    | "LHU", [|r0;r1;offset|] -> r_type load halfword r0 r1 offset
    | "LB", [|r0;r1;offset|] -> r_type load byte r0 r1 offset
    | "LBU", [|r0;r1;offset|] -> r_type load byte r0 r1 offset
    | "SW", [|r0;r1;offset|] -> r_type store word r0 r1 offset
    | "SH", [|r0;r1;offset|] -> r_type store halfword r0 r1 offset
    | "SB", [|r0;r1;offset|] -> r_type store byte r0 r1 offset
    | _ -> Ok [Bil.special (Insn.asm insn)]

    (** Branching instructions *)

let lift_branch mem ops insn =
  let addr = Memory.min_addr mem in
  match insn, ops with

  | `Bcc, [|offset; cond; _|] ->
    Branch.lift offset ~cond addr

  | `BL, [|offset; cond; _|]
  | `BL_pred, [|offset; cond; _|] ->
    Branch.lift offset ~cond ~link:true addr

  | `BX_RET, [|cond; _|] ->
    Branch.lift (`Reg `LR) ~cond ~x:true addr

  | `BX, [|target|] ->
    Branch.lift target ~x:true addr

  | `BX_pred, [|target; cond; _|] ->
    Branch.lift target ~cond ~x:true addr

  | `BLX, [|target|] ->
    Branch.lift target ~link:true ~x:true addr

  | `BLX_pred, [|target; cond; _|] ->
    Branch.lift target ~cond ~link:true ~x:true addr

  | `BLXi, [|offset|] ->
    Branch.lift offset ~link:true ~x:true addr

  | insn,ops ->
    fail [%here] "ops %s doesn't match branch insn %s"
      (string_of_ops ops) (Arm_insn.to_string (insn :> insn))


  let lift_bra mem insn = match Insn.name insn, Insn.ops insn with
    | "Bcc", [|r0;offset;cond|] -> Branch.lift offset ~cond addr
    | "Bcc", [|r0;r1;offset;cond|] -> Branch.lift offset ~cond ~comp:true addr
    | "BEQ", [|r0;r1;addr|] -> Branch.lift `EQ addr
    | "BNE", [|r0;r1;addr|] -> Branch.lift `NE addr
    | "BGE", [|r0;r1;addr|] -> Branch.lift `GE addr
    | "BLT", [|r0;r1;addr|] -> Branch.lift `LT addr
    | "BLTU", [|r0;r1;addr|] -> Branch.lift `LTU addr
    | "BGEU", [|r0;r1;addr|] -> Branch.lift `GEU addr

 (*   | "J", [|offset|] -> Branch.lift *)
    | "JAL", [|r0;addr|] -> Branch.lift ~link:true addr
 (*    | "JR", [|r0;|] *)
    | "JALR", [|r0;r2; 0|] -> Branch.lift ~link:true addr
    | "RET", [||] -> r_type ret
    | _ -> Ok [Bil.special (Insn.asm insn)]

  let lift_csr mem insn = match Insn.name insn, Insn.ops insn with
    | "CSRRW", [|r0;r1|] -> r_type load
    | "CSRRS", [|r0;r1|] -> r_type 
    | "CSRRC", [|r0;r1|] -> r_type
    | "CSRRWI", [|r0;imm|] -> r_type
    | "CSRRSI", [|r0;imm|] -> r_type
    | "CSRRCI", [|r0;imm|] -> r_type
    | _ -> Ok [Bil.special (Insn.asm insn)]

end

let () = register_target `riscv (module Riscv)
