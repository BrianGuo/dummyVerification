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
  Definition ADD_nat {S} : instruction (nat ::: nat ::: S) (nat ::: S) := ADD.
  About full_contract.
  About SEQ.
  Print Implicit full_contract.
  Arguments full_contract : default implicits.
  Definition addtwo_contract : full_contract get_contract_type parameter_ty storage_ty := (UNPAIR;; SWAP;; DROP;; UNPAIR;; ADD;; NIL operation;; PAIR).
  Check precond.
  Check addtwo_contract.
  Check Datatypes.nat.
  Check eval_precond.
  Check parameter_ty.
  Check eval.
  Definition addTwo_spec
             (param : data parameter_ty)
             (storage : data storage_ty)
             (contract: full_contract get_contract_type parameter_ty storage_ty)
             (fuel : Datatypes.nat)
             (psi : stack (pair (list_ operation) storage_ty ::: nil) -> Prop)
    :=
    (precond (eval contract fuel ((param, storage), tt)), psi).
  Check data.
  About N.
  Check comparable_data storage_ty.
  Check nat.
  Check Datatypes.nat.
  About precond. About eval. 
  Lemma addTwo_correct (t1 : N) (t2 : N) (storage : N) (fuel : Datatypes.nat) :
    let params : data parameter_ty := (t1, t2) in
    let storage : data storage_ty := storage in
    let sum : N := (t1 + t2)%N in
    10 <= fuel -> precond (eval (addtwo_contract) (fuel) ((params, storage), tt)) (fun (result : stack (pair (list_ operation) storage_ty ::: nil)) => sum = snd (fst result)) = true.
  Proof.
    intros.
    unfold eval.
    unfold addtwo_contract.  
    destruct fuel.
    - contradict H.
      easy.
    - simpl.
      unfold semantics.eval.
      destruct 
      
      discriminate.
      trivial.
    