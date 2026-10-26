(*
 * Copyright (C) 2026  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

(** A faithful implementation of the G sequent calculus *)

type form = Metaterm.metaterm

type sequent
(** A sequent is an abstract representation of
    a G sequent, ["si ; gam |- f"] *)

type error

val pp_error : Format.formatter -> error -> unit
val error_to_string : error -> string

type 'a result = ('a, error) Result.t

(** {2 Creating end-sequents} *)

(** [form_to_sequent f] is [". ; . |- f"] *)
val form_to_sequent : form -> sequent

(** [end_equent ~vars:si ~hyps:gam ~goal:f]
    is ["si ; gam |- f"] *)
val end_sequent :
  vars:(Term.id * Term.term) list ->
  hyps:(Term.id * form) list ->
  goal:form ->
  sequent result

(** {2 structural rules} *)

(** [contract "si ; gam, l:f |- r"] is
    [("si ; gam, l:f, l1:f |- r", l1)]
    for some fresh [l1] *)
val contract : left:Term.id ->
  sequent -> (sequent * Term.id) result

(** [weaken "si ; gam, l:f |- r"] is
    ["si ; gam |- r"] *)
val weaken : left:Term.id ->
  sequent -> sequent result

(** {2 Initial sequents} *)

(** [initial "si ; gam, l:f |- r"] is [()] if [f] and [r] are equivariant,
    i.e. identical up to a permutation of the nominal constants in their
    support. It fails if [l] is not in [gam] or the two are not
    equivariant. *)
val initial : left:Term.id ->
  sequent -> unit result

(** {2 Conjunction and Truth} *)

(** [and_right "si ; gam |- f /\ g"] is
    [("si ; gam |- f", "si ; gam |- g")] *)
val and_right : sequent ->
  (sequent * sequent) result

(** [top_right "si ; gam |- true"] is [()] *)
val top_right : sequent ->
  unit result

(** [and_left_1 "si ; gam, l:(f /\ g) |- r"] is
    [("si ; gam, l:(f /\ g), l1:f |- r", l1)]
    for some fresh [l1] *)
val and_left_1 : left:Term.id ->
  sequent -> (sequent * Term.id) result

(** [and_left_2 "si ; gam, l:(f /\ g) |- r"] is
    [("si ; gam, l:(f /\ g), l1:g |- r", l1)]
    for some fresh [l1] *)
val and_left_2 : left:Term.id ->
  sequent -> (sequent * Term.id) result

(** [and_left_both "si ; gam, l:(f /\ g) |- r"] is
    [("si ; gam, l:(f /\ g), l1:f, l2:g |- r", l1, l2)]
    for some fresh [l1] and [l2] *)
val and_left_both : left:Term.id ->
  sequent -> (sequent * Term.id * Term.id) result

(** {2 Disjunction and False} *)

(** [or_right_1 "si ; gam |- f \/ g"] is ["si ; gam |- f"] *)
val or_right_1 : sequent ->
  sequent result

(** [or_right_2 "si ; gam |- f \/ g"] is ["si ; gam |- g"] *)
val or_right_2 : sequent ->
  sequent result

(** [false_left "si ; gam |- false"] is [()] *)
val false_left : sequent ->
  unit result

(** [or_left "si ; gam, l:(f \/ g) |- r"] is
    [("si ; gam, l:(f \/ g), l1:f |- r", l1,
      "si ; gam, l:(f \/ g), l2:g |- r", l2)]
    for some fresh [l1] and [l2] *)
val or_left : left:Term.id ->
  sequent -> (sequent * Term.id * sequent * Term.id) result

(** {2 Implication} *)

(** [imp_right "si ; gam |- f -> g"] is ["si ; gam, l1:f |- g"]
    for some fresh [l1] *)
val imp_right : sequent ->
  (sequent * Term.id) result

(** [imp_left "si ; gam, l:(f -> g) |- r"] is
    [("si ; gam, l:(f -> g), l1:g |- r", l1, "si ; gam, l:(f -> g) |- f")]
    for some fresh [l1] (major premise first, then minor) *)
val imp_left : left:Term.id ->
  sequent -> (sequent * Term.id * sequent) result

(** {2 Universal quantification} *)

(** [forall_right "si ; gam |- forall x. f"] is
    [("si, x:(c : ty') ; gam |- f[x := c]", c)]
    where [c] is a fresh Eigen variable at [ty], raised over the
    support of [f]. A single binder is peeled off; any remaining binders
    stay quantified. *)
val forall_right : sequent ->
  (sequent * Term.id) result

(** [forall_left ~witness "si ; gam, l:(forall x. f) |- r"] is
    [("si ; gam, l:(forall x. f), l1:f[x := witness] |- r", l1)]
    for some fresh [l1], provided [witness] has the type of [x] and is well
    typed over the eigen variables in [si]. A single binder is peeled off;
    any remaining binders stay quantified. *)
val forall_left : left:Term.id ->
  witness:Term.term ->
  sequent -> (sequent * Term.id) result

(** {2 Existential quantification} *)

(** [exists_right ~witness "si ; gam |- exists x. f"] is
    ["si ; gam |- f[x := witness]"], provided [witness] has the type of [x]
    and is well typed over the eigen variables in [si]. A single binder is
    peeled off; any remaining binders stay quantified. *)
val exists_right : witness:Term.term ->
  sequent -> sequent result

(** [exists_left "si ; gam, l:(exists x. f) |- r"] is
    [("si, x:(c : ty') ; gam, l:(exists x. f), l1:f[x := c] |- r", l1)]
    where [c] is a fresh Eigen variable at [ty], raised over the support
    of [f]. A single binder is peeled off; any remaining binders
    stay quantified. *)
val exists_left : left:Term.id ->
  sequent -> (sequent * Term.id) result

(** {2 Generic quantification (nabla)} *)

(** [nabla_right "si ; gam |- nabla x. f"] is
    [("si, x:(n : ty) ; gam |- f[x := n]", n)]
    where [n] is a fresh nominal constant. A single binder is peeled off; any
    remaining binders stay quantified. *)
val nabla_right : sequent ->
  (sequent * Term.id) result

(** [nabla_left "si ; gam, l:(nabla x. f) |- r"] is
    [("si, x:(n : ty) ; gam, l:(nabla x. f), l1:f[x := n] |- r", l1)]
    where [n] is a fresh nominal constant. A single binder is peeled off; any
    remaining binders stay quantified. *)
val nabla_left : left:Term.id ->
  sequent -> (sequent * Term.id) result
