(*
 * Author: Kaustuv Chaudhuri <kaustuv@chaudhuri.info>
 * Copyright (C) 2026  Inria
 * See LICENSE for licensing details.
 *)

(* An implementation of focused LJ= search with search depths *)

open! Term
open! Typing
open! Metaterm
open! Abella_types
open! Extensions

type bound =
  | Decide_depth of int
  | Unbounded

exception Search_bounds

let reduce_bound = function
  | Decide_depth n when n > 0 ->
      Decide_depth (n - 1)
  | Decide_depth _ ->
      raise Search_bounds
  | Unbounded ->
      Unbounded

type zone = (id * metaterm) list

type sequent = {
  left_passive : zone ;
  left_active : zone ;
  right : metaterm * [`active | `passive] ;
}

type derivation = {
  end_sequent : sequent ;
  proof : proof ;
}

and proof =
  | Unfinished
  | Decide_right of {
      prem : rf_proof ;
    }
  | Decide_left of {
      hyp : id ;
      prem : lf_proof ;
    }

(* right focused proof *)
and rf_proof =
  | Rf_init of {
      hyp : id ;
      prem : rf_eq_proof ;
    }
  | Rf_and of {
      prem1 : rf_proof ;
      prem2 : rf_proof ;
    }
  | Rf_top
  | Rf_or of {
      choice : [`l | `r] ;
      prem : rf_proof ;
    }
  | Rf_ex of {
      evar : var ;
      prem : rf_proof ;
    }
  | Rf_eq of {
      prem : rf_eq_proof
    }
  | Rf_release of {
      prem : ra_proof ;
    }

(* right active proof *)
and ra_proof =
  | Ra_imp of {
      prem : ra_proof ;
    }
  | Ra_all of {
      uvar : var ;
      prem : ra_proof ;
    }
  | Ra_store of {
      prem : la_proof ;
    }

(* left focused proof *)
and lf_proof =
  | Lf_init of {
      prem : rf_eq_proof ;
    }
  | Lf_imp of {
      prem_ante : rf_proof ;
      prem_conc : lf_proof ;
    }
  | Lf_all of {
      evar : var ;
      prem : lf_proof ;
    }
  | Lf_release of {
      prem : la_proof ;
    }

(* left active proof *)
and la_proof =
  | Lf_and of {
      prem : la_proof ;
    }
  | Lf_top of {
      prem : la_proof ;
    }
  | La_or of {
      prem1 : la_proof ;
      prem2 : la_proof ;
    }
  | La_bot
  | La_ex of {
      uvar : var ;
      prem : la_proof ;
    }
  | La_store of {
      hyp : id ;
      prem : la_proof ;
    }
  | La_eq of {
      lhs : term ;
      rhs : term ;
      prem : la_proof ;
    }

(* note: these are all focused, so no suspensions *)
and rf_eq_proof =
  | Rf_eq_symm of {
      prem : rf_eq_proof ;
    }
  | Rf_eq_refl of {
      lhs : term ;
      rhs : term ;
      (* no premises *)
    }
  | Rf_eq_mimic of {
      evar : var ;
      rhs : term ;
      prems : rf_eq_proof list ;
    }
  | Rf_eq_descend of {
      lhs : term ;
      rhs : term ;
      prems : rf_eq_proof list ;
    }
