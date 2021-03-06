(*
    ||M||  This file is part of HELM, an Hypertextual, Electronic        
    ||A||  Library of Mathematics, developed at the Computer Science     
    ||T||  Department, University of Bologna, Italy.                     
    ||I||                                                                
    ||T||  HELM is free software; you can redistribute it and/or         
    ||A||  modify it under the terms of the GNU General Public License   
    \   /  version 2 or (at your option) any later version.      
     \ /   This software is distributed as is, NO WARRANTY.     
      V_______________________________________________________________ *)

type outcome = Skip of string
             |         Fail
             |         OK
             |         Timeout

(* use this kernel: valid values "NO" (default), "CSC", "FG0", "FG1" *)
val set_kernel_from_string: string -> unit

(* trace options *)
val trace_options : string list ref

(* computation length *)
val maxsteps : int ref

(* run elpi typechecker *)
val typecheck : bool ref

(* turn informational prints off *)
val prints_off: unit -> unit

(* turn cache on *)
val cache_on: unit -> unit

(* actions to take at exit, if any *)
val at_exit: unit -> unit

(* execute kernel queries: is_type, has_type *)
val validate: bool ref

(* execute refiner queries: approx, approx_cast *)
val refine: bool ref

(* is_type r u is OK if the type of u is a sort *)
val is_type: #NCic.status -> NReference.reference -> NCic.term -> float * outcome

(* has_type r t u is OK if the type of t is u *)
val has_type: #NCic.status -> NReference.reference -> NCic.term -> NCic.term -> float * outcome

(* approx r c s1 t s2 v w is OK if (s2, c, v) of inferred type (s2, c, w) refines (s1, c, t) *)
val approx: #NCic.status -> NReference.reference -> NCic.context ->
  NCic.substitution -> NCic.term ->
  NCic.substitution -> NCic.term -> NCic.term ->
  float * outcome

(* approx_cast r c s1 t u s2 v is OK if (s2, c, v) refines (s1, c, t) of expected type (s1, c, u) *)
val approx_cast: #NCic.status -> NReference.reference -> NCic.context ->
  NCic.substitution -> NCic.term -> NCic.term ->
  NCic.substitution -> NCic.term ->
  float * outcome

val set_apply_subst:
 (NCic.status -> NCic.substitution -> NCic.context -> NCic.term -> NCic.term)
 -> unit
