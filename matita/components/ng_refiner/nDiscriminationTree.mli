(* Copyright (C) 2005, HELM Team.
 * 
 * This file is part of HELM, an Hypertextual, Electronic
 * Library of Mathematics, developed at the Computer Science
 * Department, University of Bologna, Italy.
 * 
 * HELM is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 * 
 * HELM is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with HELM; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston,
 * MA  02111-1307, USA.
 * 
 * For details, see the HELM World-Wide-Web page,
 * http://cs.unibo.it/helm/.
 *)

module NCicIndexable : Discrimination_tree.Indexable
with type input = NCic.term and type constant_name = NReference.reference

module TermSet : Set.S with type elt = NCic.term
module TermListSet : Set.S with type elt = NCic.term list

module DiscriminationTree : Discrimination_tree.DiscriminationTree 
with type constant_name = NCicIndexable.constant_name 
and type input = NCicIndexable.input
and type data = TermSet.elt and type dataset = TermSet.t
