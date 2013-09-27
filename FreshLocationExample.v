(* DOES NOT SEEM TO LEAD ANYWHERE *)
Require Import SfLib.


(* Import the FMapList library *)
Require Import Coq.FSets.FMapList.
(* Import the OrderedType module for natural numbers *)
Require Import Coq.Structures.OrderedTypeEx.

(* This is the location module *)
Module Loc := Nat_as_OT.
(* Define a module for our Map (i.e. heap) *)
Module Map := Raw (Loc).

Hypothesis tmS : Type.
Hypothesis tmL : Type.

Definition heapS : Type := Map.t tmS.
Definition heapL : Type := Map.t tmL.

Hypothesis step : forall {tm : Type} {heap : Type},
                    nat -> (tm * heap) -> (tm * heap) -> Prop.


Definition mapping_length {elt : Type} (m : Map.t elt) : nat :=
  Map.fold (fun _ _ => plus 1) m 0.


Inductive multistep {tm : Type} {heap : Type} :
  list nat -> (tm * heap) -> (tm * heap) -> Prop :=
  ms_refl : forall e h , multistep [] (e, h) (e, h)
| ms_step : forall e h e' h' e'' h'' n l,
               step n (e, h) (e', h') ->
               multistep l (e', h') (e'', h'') ->
               multistep (n :: l) (e, h) (e'', h'')
.

Hypothesis proj : (tmS * heapS) -> (tmL * heapL).

Hypothesis projection_step : forall eS eS' hS hS' n,
                          step n (eS, hS) (eS', hS') ->
                       multistep [n] (proj (eS, hS)) (proj (eS', hS')).

Lemma determinsticL : forall ns cfg cfg1' cfg2',
                        multistep ns cfg cfg1' ->
                        multistep ns cfg cfg2' ->
                        cfg1' = cfg2'


Theorem projection : forall eS eS' hS hS' ns,
                       multistep ns (eS, hS) (eS', hS') ->
                       multistep ns (proj (eS, hS)) (proj (eS', hS')).

  (* Problem: multistepL is not deterministic *)
  (* Problem: how to guarantee that n is fresh for h *)


