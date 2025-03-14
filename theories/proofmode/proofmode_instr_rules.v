From cap_machine Require Import rules.
From Ltac2 Require Import Ltac2 Option.
Set Default Proof Mode "Classic".

Ltac dispatch_Get r1 r2 cont :=
  let p := constr:((r1, r2)) in
  lazymatch p with
  | (_, PC) => cont (@wp_Get_PC_success)
  | (?r, ?r) => cont (@wp_Get_same_success)
  | _ => cont (@wp_Get_success)
  end.

Ltac dispatch_AddSubLt r1 x1 x2 cont :=
  let p := constr:((r1, x1, x2)) in
  lazymatch p with
  | (?r, (inr ?r), (inr ?r)) => cont (@wp_add_sub_lt_success_dst_dst)
  | (?dst, (inr ?r), (inr ?dst)) => cont (@wp_add_sub_lt_success_r_dst)
  | (?dst, (inr ?dst), (inr ?r)) => cont (@wp_add_sub_lt_success_dst_r)
  | (?dst, (inl _), (inr ?dst)) => cont (@wp_add_sub_lt_success_z_dst)
  | (?dst, (inr ?dst), (inl _)) => cont (@wp_add_sub_lt_success_dst_z)
  | (?dst, (inr ?r), (inr ?r)) => cont (@wp_add_sub_lt_success_r_r_same)
  | (?dst, (inr ?r), (inl _)) => cont (@wp_add_sub_lt_success_r_z)
  | (?dst, (inl _), (inr _)) =>
    (cont (@wp_add_sub_lt_success_z_r) ||
     cont (@wp_add_sub_lt_fail_z_r))
  | (?dst, (inr _), (inr _)) => cont (@wp_add_sub_lt_success_r_r)
  | (?dst, (inl _), (inl _)) => cont (@wp_add_sub_lt_success_z_z)
  end.

Ltac dispatch_instr_rule instr cont :=
  let instr := eval unfold machine_base.regn, machine_base.cst in instr in
  lazymatch instr with
  (* Mov *)
  | Mov PC (inr PC) => cont (@wp_move_success_reg_samePC)
  | Mov PC (inr _) => cont (@wp_move_success_reg_toPC)
  | Mov _ (inr PC) => cont (@wp_move_success_reg_fromPC)
  | Mov ?r (inr ?r) => cont (@wp_move_success_reg_same)
  | Mov _ (inr _) => cont (@wp_move_success_reg)
  | Mov _ (inl _) => cont (@wp_move_success_z)
  (* Get *)
  | GetP ?r1 ?r2 => dispatch_Get r1 r2 cont
  | GetB ?r1 ?r2 => dispatch_Get r1 r2 cont
  | GetE ?r1 ?r2 => dispatch_Get r1 r2 cont
  | GetA ?r1 ?r2 => dispatch_Get r1 r2 cont
  | GetOType ?r1 ?r2 => dispatch_Get r1 r2 cont
  | GetWType ?r1 ?r2 => dispatch_Get r1 r2 cont
  (* AddSubLt *)
  | Add ?x1 ?x2 ?x3 => dispatch_AddSubLt x1 x2 x3 cont
  | Sub ?x1 ?x2 ?x3 => dispatch_AddSubLt x1 x2 x3 cont
  | Mod ?x1 ?x2 ?x3 => dispatch_AddSubLt x1 x2 x3 cont
  | HashConcat ?x1 ?x2 ?x3 => dispatch_AddSubLt x1 x2 x3 cont
  | Lt ?x1 ?x2 ?x3 => dispatch_AddSubLt x1 x2 x3 cont
  (* Lea *)
  | Lea PC (inr _) => cont (@wp_lea_success_reg_PC)
  | Lea PC (inl _) => cont (@wp_lea_success_z_PC)
  | Lea _ (inr _) => (cont (@wp_lea_success_reg) || cont (@wp_lea_success_reg_sr))
  | Lea _ (inl _) => (cont (@wp_lea_success_z) || cont (@wp_lea_success_z_sr))
  (* Load *)
  | Load PC _ => cont (@wp_load_success_PC)
  | Load _ PC => cont (@wp_load_success_fromPC)
  | Load ?r ?r =>
    (cont (@wp_load_success_same_notinstr) ||
     cont (@wp_load_success_same_frominstr))
  | Load _ _ =>
    (cont (@wp_load_success_notinstr) ||
     cont (@wp_load_success_frominstr))
  (* Store *)
  | Store PC (inl _) => cont (@wp_store_success_z_PC)
  | Store PC (inr PC) => cont (@wp_store_success_reg_PC_same)
  | Store PC (inr _) => cont (@wp_store_success_reg_PC)
  | Store _ (inl _) =>
    (cont (@wp_store_success_same) ||
     cont (@wp_store_success_z))
  | Store _ (inr PC) =>
    (cont (@wp_store_success_reg_frominstr_same) ||
     cont (@wp_store_success_reg_frominstr))
  | Store ?r (inr ?r) =>
    (cont (@wp_store_success_reg_same') ||
     cont (@wp_store_success_reg_same))
  | Store _ (inr _) =>
    (cont (@wp_store_success_reg_same_a) ||
     cont (@wp_store_success_reg))
  (* Jnz *)
  | Jnz PC PC => cont (@wp_jnz_success_jmpPC)
  | Jnz ?r PC => cont (@wp_jnz_success_jmpPC2)
  | Jnz _ _ =>
    (cont (@wp_jnz_success_next) ||
    (lazymatch instr with
     | Jnz PC _ => cont (@wp_jnz_success_jmpPC1)
     | Jnz ?r ?r => cont (@wp_jnz_success_jmp2)
     | Jnz _ _ => cont (@wp_jnz_success_jmp)
     end))
  (* Jmp *)
  | Jmp PC => cont (@wp_jmp_successPC)
  | Jmp _ => cont (@wp_jmp_success)
  (* Subseg *)
  | Subseg PC (inr ?r) (inr ?r) => cont (@wp_subseg_success_pc_same)
  | Subseg PC (inr _) (inr _) => cont (@wp_subseg_success_pc)
  | Subseg PC (inl _) (inr _) => cont (@wp_subseg_success_pc_l)
  | Subseg PC (inr _) (inl _) => cont (@wp_subseg_success_pc_r)
  | Subseg PC (inl _) (inl _) => cont (@wp_subseg_success_pc_lr)
  | Subseg _ (inr ?r) (inr ?r) => (cont (@wp_subseg_success_same) || cont (@wp_subseg_success_same_sr)) (* TODO: improve using register values? *)
  | Subseg _ (inr _) (inr _) => (cont (@wp_subseg_success) || cont (@wp_subseg_success_sr))
  | Subseg _ (inl _) (inr _) => (cont (@wp_subseg_success_l) || cont (@wp_subseg_success_l_sr))
  | Subseg _ (inr _) (inl _) => (cont (@wp_subseg_success_r) || cont (@wp_subseg_success_r_sr))
  | Subseg _ (inl _) (inl _) => (cont (@wp_subseg_success_lr) || cont (@wp_subseg_success_lr_sr))
  (* Restrict *)
  | Restrict PC (inr _) => cont (@wp_restrict_success_reg_PC)
  | Restrict _ (inr _) => cont (@wp_restrict_success_reg)
  | Restrict PC (inl _) => cont (@wp_restrict_success_z_PC)
  | Restrict _ (inl _) => cont (@wp_restrict_success_z)
  (* Seal *)
  | Seal ?r ?r PC => cont (@wp_seal_PC_eq)
  | Seal _ _ PC => cont (@wp_seal_PC)
  | Seal ?r _ ?r => cont (@wp_seal_r2)
  | Seal ?r ?r _ => cont (@wp_seal_r1)
  | Seal _ _ _ => cont (@wp_seal_success)
  (* UnSeal *)
  | UnSeal PC _ _ => cont (@wp_unseal_PC)
  | UnSeal ?r _ ?r => cont (@wp_unseal_r2)
  | UnSeal ?r ?r _ => cont (@wp_unseal_r1)
  | UnSeal _ _ _ => cont (@wp_unseal_success)
  (* IsUnique*)
  | IsUnique _ _ => cont (@wp_isunique_success)
  (* Fail *)
  | Fail => cont (@wp_fail)
  (* Halt *)
  | Halt => cont (@wp_halt)
  (* not found *)
  (* TODO @Denis EInit, EDeInit, EStoreId *)
  (* TODO @June IsUnique *)
  | _ => fail "No suitable rule found for instruction" instr
  end.
