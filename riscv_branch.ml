open Core_kernel.Std
open Bap.Std
open Or_error

open Riscv_types

let pc_offset = Word.of_int ~width:32
let word = Word.of_int ~width:32

let lift operand ?link ?cond addr =
  let target =
    match operand with
    | `Reg r -> Bil.var (Env.of_reg r)
    | `Imm offset ->
      let width = Word.bitwidth offset in
      let _1 = Word.one 32 in
      let min_32 = Word.Int_exn.(_1 lsl Word.of_int 31 ~width) in
      let offset = if offset = min_32 then Word.zero 32 else offset in
      let r = Word.Int_exn.(addr + pc_offset + offset) in
      Bil.int r in
  let jump_instr = [Bil.jmp target] in
  let link_instr =
    let next_addr = Word.Int_exn.(addr + pc_offset - word 4) in
    match link with
    | Some true -> [Bil.move Env.lr Bil.(int next_addr)]
    | _         -> [] in
  let stmts = link_instr @ jump_instr in
  match cond with
  | Some c -> exec stmts c
  | None -> stmts
