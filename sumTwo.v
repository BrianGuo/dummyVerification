Add LoadPath "../mi-cho-coq/src/michocoq/" as Michocoq.
Require Import Michocoq.macros.
Import syntax.
Import comparable.
Require Import NArith.
Require Import Michocoq.semantics.
Import error.
Require List.
Import BinNatDef.
Section addtwo.

  Definition parameter_ty := (pair nat nat).
  Definition storage_ty := nat.
  Context {get_contract_type : contract_constant -> error.M type} {env : @proto_env get_contract_type parameter_ty}.
  Check get_contract_type.
  Definition instruction := @syntax.instruction get_contract_type parameter_ty.
  Definition data := @semantics.data get_contract_type parameter_ty.
  Definition stack := @semantics.stack get_contract_type parameter_ty.
  Definition eval {A B : stack_type} := @semantics.eval _ _ env A B.
  Definition eval_precond := @semantics.eval_precond _ _ env.  
  Arguments full_contract : default implicits.
  Definition addtwo_contract : full_contract get_contract_type parameter_ty storage_ty := (UNPAIR;; SWAP;; DROP;; UNPAIR;; ADD;; NIL operation;; PAIR).
  Ltac mysimpl :=
  match goal with
    |- ?g =>
    match g with
    | context c[semantics.eval_precond ?env (S ?n) ?i ?psi] =>
      is_var i ||
             (let simplified := (eval simpl in (semantics.eval_precond env (S n) i psi)) in
              let full := context c[simplified] in
              let final := eval cbv beta zeta iota in full in
              change final)
    end
  end.

  Ltac more_fuel :=
  match goal with
    | Hfuel : (_ <= ?fuel) |- _ =>
      destruct fuel as [|fuel];
      [inversion Hfuel; fail
      | apply le_S_n in Hfuel]
  end.

  Lemma addTwo_correct (t1 : N) (t2 : N) (storage : N) (fuel : Datatypes.nat) :
    let params : data parameter_ty := (t1, t2) in
    let storage : data storage_ty := storage in
    let sum : N := (t1 + t2)%N in
    10 <= fuel -> precond (eval (addtwo_contract) (fuel) ((params, storage), tt)) (fun (result : stack (pair (list_ operation) storage_ty ::: nil)) => sum = snd (fst result)).
  Proof.
    intros.
    unfold eval.
    unfold addtwo_contract.   
    rewrite eval_precond_correct.
    do 10 more_fuel.
    mysimpl.
    simpl.
    trivial.
Qed.    