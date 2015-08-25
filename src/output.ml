(* This file is part of Abella
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2015  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See COPYING for licensing details.
 *)

let out = ref Format.std_formatter
let out_printf fmt = Format.fprintf !out fmt

let err = ref Format.err_formatter
let err_printf fmt = Format.fprintf !err fmt
