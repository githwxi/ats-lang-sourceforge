(***********************************************************************)
(*                                                                     *)
(*                         Applied Type System                         *)
(*                                                                     *)
(*                              Hongwei Xi                             *)
(*                                                                     *)
(***********************************************************************)

(*
 * ATS - Unleashing the Power of Types!
 *
 * Copyright (C) 2002-2007 Hongwei Xi, Boston University
 *
 * All rights reserved
 *
 * ATS is free software;  you can  redistribute it and/or modify it under
 * the terms of the GNU LESSER GENERAL PUBLIC LICENSE as published by the
 * Free Software Foundation; either version 2.1, or (at your option)  any
 * later version.
 * 
 * ATS is distributed in the hope that it will be useful, but WITHOUT ANY
 * WARRANTY; without  even  the  implied  warranty  of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the  GNU General Public License
 * for more details.
 * 
 * You  should  have  received  a  copy of the GNU General Public License
 * along  with  ATS;  see the  file COPYING.  If not, please write to the
 * Free Software Foundation,  51 Franklin Street, Fifth Floor, Boston, MA
 * 02110-1301, USA.
 *
 *)

(* ****** ****** *)

(* author: Hongwei Xi (hwxi AT cs DOT bu DOT edu) *)

(* ****** ****** *)

implement dynload_dummy () = () // no need for dynamic loading

(* ****** ****** *)

// list implementation

#define nil list_nil
#define cons list_cons
#define :: list_cons

(* ****** ****** *)

// a tail-recursive implementation of list-append

implement list_append<a> {i,j} (xs, ys) = let
  var res: List a // uninitialized
  fun aux {n1,n2:nat} .<n1>.
    (xs: list (a, n1), ys: list (a, n2), res: &(List a)? >> list (a, n1+n2))
    :<> void = begin case+ xs of
    | x :: xs => let
        val () = (res := cons {a} {0} (x, ?)); val cons (_, !p) = res
      in
        aux (xs, ys, !p); fold@ res
      end
    | nil () => (res := ys)
  end // end of [aux]
in
  aux (xs, ys, res); res
end

(*

// standard non-tail-recursive implementation of list-append

implement list_append<a> {i,j} (xs, ys) = let
  fun aux {n1,n2:nat} .<n1>.
    (xs: list (a, n1), ys: list (a, n2)):<> list (a, n1+n2) =
    case+ xs of x :: xs => x :: aux (xs, ys) | nil () => ys
in
  aux (xs, ys)
end

*)

//

implement list_assoc_fun<a1,a2> {eq:eff} (xys, eq, x0) = let
  fun aux {n:nat} .<n>. (xys: list ('(a1, a2), n)):<eq> Option a2 =
    case+ xys of
    | '(x, y) :: xys => if eq (x0, x) then Some (y) else aux xys
    | nil () => None ()
in
  aux xys
end

//

implement list_concat<a> (xss) = let
  fun aux {n:nat} .<n>.
    (xs0: List a, xss: list (List a, n)):<> List a =
    case+ xss of
    | xs :: xss => list_append (xs0, aux (xs, xss))
    | nil () => xs0
in
  case+ xss of xs :: xss => aux (xs, xss) | nil () => nil ()
end

//

implement list_drop<a> (xs, i) = let
  fun aux {n,i:nat | i <= n} .<i>.
    (xs: list (a, n), i: int i):<> list (a, n-i) =
    if i > 0 then let val _ :: xs = xs in aux (xs, i-1) end
    else xs
in
  aux (xs, i)
end

(* ****** ****** *)

implement list_exists_main<a> (pf | xs, p, env) = begin
  case+ xs of
  | x :: xs => begin
      if p (pf | x, env) then true
      else begin
        list_exists_main (pf | xs, p, env)
      end
    end
  | nil () => false
end // end of [list_exists_main]

implement list_exists_cloptr<a> {p:eff} (xs, p) = let
  viewtypedef cloptr_t = a -<cloptr,p> bool
  fn app (pf: !unit_v | x: a, p: !cloptr_t):<p> bool = p (x)
  prval pf = unit_v ()
  val ans = list_exists_main<a> {unit_v} {cloptr_t} (pf | xs, app, p)
  prval unit_v () = pf
in
  ans
end // end of [list_exists_cloptr]

implement list_exists2_main<a1,a2>
  (pf | xs1, xs2, p, env) = begin case+ xs1 of
  | x1 :: xs1 => let
      val+ x2 :: xs2 = xs2
    in
      if p (pf | x1, x2, env) then true
      else begin
        list_exists2_main (pf | xs1, xs2, p, env)
      end
    end
  | nil () => false
end // end of [list_exists2_main]

implement list_exists2_cloptr<a1,a2> {n} {p:eff} (xs1, xs2, p) = let
  viewtypedef clo_t = (a1, a2) -<cloptr,p> bool
  fn app (pf: !unit_v | x1: a1, x2: a2, p: !clo_t):<p> bool = p (x1, x2)
  prval pf = unit_v ()
  val ans = list_exists2_main<a1,a2> {unit_v} {clo_t} (pf | xs1, xs2, app, p)
  prval unit_v () = pf
in
  ans
end // end of [list_exists2_cloptr]

(* ****** ****** *)

implement list_filter_cloptr<a> (xs, p) = begin
  case+ xs of
  | x :: xs => begin
      if p (x) then x :: list_filter_cloptr (xs, p)
      else list_filter_cloptr (xs, p)
    end
  | nil () => nil ()
end // end of [list_filter_cloptr]

(* ****** ****** *)

implement list_find_cloptr<a> (xs, p) = begin case+ xs of
  | x :: xs => if p (x) then Some (x) else list_find_cloptr (xs, p)
  | nil () => None ()
end // end of [list_find_cloptr]

(* ****** ****** *)

(*

macrodef list_fold_left_mac (list_fold_left, f, res, xs) = `(
  case+ ,(xs) of
  | x :: xs => ,(list_fold_left) (,(f), ,(f) (,(res), x), xs)
  | nil () => ,(res)
)

*)

implement list_fold_left_cloptr<sink,a> (f, res, xs) = begin
  case+ xs of
  | x :: xs => list_fold_left_cloptr (f, f (res, x), xs)
  | nil () => res
end // end of [list_fold_left_cloptr]

implement list_fold2_left_cloptr<sink,a1,a2> (f, res, xs1, xs2) = begin
  case+ xs1 of
  | x1 :: xs1 => let
      val+ x2 :: xs2 = xs2; val res = f (res, x1, x2)
    in
      list_fold2_left_cloptr (f, res, xs1, xs2)
    end
  | nil () => res
end // end of [list_fold2_left_cloptr]

(* ****** ****** *)

implement list_fold_right_cloptr<a,sink> (f, xs, res) = begin
  case+ xs of
  | x :: xs => begin
      let val res = list_fold_right_cloptr (f, xs, res) in f (x, res) end
    end
  | nil () => res
end // end of [list_fold_right_cloptr]

implement list_fold2_right_cloptr<a1,a2,sink> (f, xs1, xs2, res) = begin
  case+ xs1 of
  | x1 :: xs1 => let
      val+ x2 :: xs2 = xs2
      val res = list_fold2_right_cloptr (f, xs1, xs2, res)
    in
      f (x1, x2, res)
    end
  | nil () => res
end // end of [list_fold2_right_cloptr]

(* ****** ****** *)

implement list_forall_main<a> (pf | xs, p, env) = begin
  case+ xs of
  | x :: xs => begin
      if p (pf | x, env) then list_forall_main (pf | xs, p, env)
      else false
    end
  | nil () => false
end // end of [list_forall_main]

implement list_forall_cloptr<a> {p:eff} (xs, p) = let
  viewtypedef cloptr_t = a -<cloptr,p> bool
  fn app (pf: !unit_v | x: a, p: !cloptr_t):<p> bool = p (x)
  prval pf = unit_v ()
  val ans = list_forall_main<a> {unit_v} {cloptr_t} (pf | xs, app, p)
  prval unit_v () = pf
in
  ans
end // end of [list_forall_cloptr]

implement list_forall2_main<a1,a2>
  (pf | xs1, xs2, p, env) = begin case+ xs1 of
  | x1 :: xs1 => let
      val+ x2 :: xs2 = xs2
    in
      if p (pf | x1, x2, env) then
        list_forall2_main (pf | xs1, xs2, p, env)
      else false
    end
  | nil () => false
end // end of [list_forall2_main]

implement list_forall2_cloptr<a1,a2> {n} {p:eff} (xs1, xs2, p) = let
  viewtypedef clo_t = (a1, a2) -<cloptr,p> bool
  fn app (pf: !unit_v | x1: a1, x2: a2, p: !clo_t):<p> bool = p (x1, x2)
  prval pf = unit_v ()
  val ans = list_forall2_main<a1,a2> {unit_v} {clo_t} (pf | xs1, xs2, app, p)
  prval unit_v () = pf
in
  ans
end // end of [list_forall2_cloptr]

(* ****** ****** *)

implement list_foreach_main<a> (pf | xs, f, env) = begin
  case+ xs of
  | x :: xs => begin
      f (pf | x, env); list_foreach_main<a> (pf | xs, f, env)
    end
  | nil () => ()
end // end of [list_foreach]

implement list_foreach_cloptr<a> {f:eff} (xs, f) = let
  viewtypedef cloptr_t = a -<cloptr,f> void
  fn app (pf: !unit_v | x: a, f: !cloptr_t):<f> void = f (x)
  prval pf = unit_v ()
  val () = list_foreach_main<a> {unit_v} {cloptr_t} (pf | xs, app, f)
  prval unit_v () = pf
in
  // empty
end // end of [list_foreach_cloptr]

implement list_foreach2_main<a1,a2> (pf | xs1, xs2, f, env) = begin
  case+ xs1 of
  | x1 :: xs1 => let
      val x2 :: xs2 = xs2
    in
      f (pf | x1, x2, env); list_foreach2_main (pf | xs1, xs2, f, env)
    end
  | nil () => ()
end // end of [list_foreach2_main]

implement list_foreach2_cloptr<a1,a2> {n} {f:eff} (xs1, xs2, f) = let
  viewtypedef cloptr_t = (a1, a2) -<cloptr,f> void
  fn app (pf: !unit_v | x1: a1, x2: a2, f: !cloptr_t):<f> void =
    f (x1, x2)
  prval pf = unit_v ()
  val () = begin
    list_foreach2_main<a1,a2> {unit_v} {cloptr_t} (pf | xs1, xs2, app, f)
  end
  prval unit_v () = pf
in
  // empty
end // end of [list_foreach2_cloptr]

(* ****** ****** *)

implement list_iforeach_cloptr<a> {n} {f:eff} (xs, f) = let
  viewtypedef cloptr_t = (natLt n, a) -<cloptr,f> void
  fun aux {i,j:nat | i+j==n} .<j>.
    (i: int i, xs: list (a, j), f: !cloptr_t) :<f> void = begin
    case+ xs of x :: xs => (f (i, x); aux (i+1, xs, f)) | nil () => ()
  end // end of [aux]
in
  aux (0, xs, f)
end // end of [list_iforeach]

implement list_iforeach2_cloptr<a1,a2> {n} {f:eff} (xs1, xs2, f) = let
  viewtypedef cloptr_t = (natLt n, a1, a2) -<cloptr,f> void
  fun aux {i,j:nat | i+j==n} .<j>.
    (i: int i, xs1: list (a1, j), xs2: list (a2, j), f: !cloptr_t)
    :<f> void = begin case+ (xs1, xs2) of
    | (x1 :: xs1, x2 :: xs2) => (f (i, x1, x2); aux (i+1, xs1, xs2, f))
    | (nil (), nil ()) => ()
  end // end of [aux]
in
  aux (0, xs1, xs2, f)
end // end of [list_iforeach2_cloptr]

(* ****** ****** *)

implement list_get_elt_at<a> (xs, n) = let
  fun aux {n,i:nat | i < n} .<n>.
    (xs: list (a, n), i: int i):<> a = let
    val x :: xs = xs
  in
    if i > 0 then aux (xs, pred i) else x
  end // end of [aux]
in
  aux (xs, 0)
end // end of [list_get_elt_at]

implement list_nth = list_get_elt_at

implement list_get_elt_at_exn<a> (xs, n) = let
  fun aux {n,i:nat} .<n>. 
    (xs: list (a, n), i: int i):<!exn> [n>0] a = begin
    case+ xs of
    | x :: xs => if i > 0 then aux (xs, pred i) else x
    | nil () => $raise ListSubscriptException ()
  end // end of [aux]
in
  aux (xs, 0)
end // end of [list_get_elt_at_exn]

implement list_nth_exn = list_get_elt_at_exn

implement list_get_elt_at_opt<a> (xs, n) = let
  fun aux {n,i:nat} .<n>.
    (xs: list (a, n), i: int i):<> Option a = begin
    case+ xs of
    | x :: xs => if i > 0 then aux (xs, pred i) else Some x
    | nil () => None ()
  end // end of [aux]
in
  aux (xs, 0)
end // end of [list_get_elt_at_opt]

implement list_nth_opt = list_get_elt_at_opt

(* ****** ****** *)

implement list_head (xs) = let val x :: _ = xs in x end
implement list_head_exn (xs) = case xs of
  | x :: _ => x
  | nil () => $raise ListSubscriptException

(* ****** ****** *)

implement list_is_empty (xs) = begin
  case+ xs of cons _ => false | nil _ => true
end // end of [list_is_empty]

implement list_is_not_empty (xs) = begin
  case+ xs of _ :: _ => true | nil () => false
end // end of [list_is_not_empty]

(* ****** ****** *)

implement list_length<a> (xs) = let
  fun aux {i,j:nat} .<i>.
    (xs: list (a, i), j: int j):<> int (i+j) = begin
    case+ xs of  _ :: xs => aux (xs, isucc j) | nil () => j
  end // end of [aux]
in
  aux (xs, 0)
end // end of [list_length]

(* ****** ****** *)

implement list_make_elt<a> (x, n) = let
  fun aux {i,j:nat} .<i>.
    (i: int i, res: list (a, j)):<> list (a, i+j) =
    if i > 0 then aux (i-1, x :: res) else res
in
  aux (n, nil)
end // end of [list_make_elt]

(* ****** ****** *)

implement list_map_main<a,b>
  {v} {vt} {n} {f:eff} (pf | xs, f, env) = let
  typedef fun_t = (!v | a, !vt) -<fun,f> b
  fun aux {n:nat} .<n>.
    (pf: !v | xs: list (a, n), f: fun_t, res: &(List b)? >> list (b, n), env: !vt)
    :<f> void = begin case+ xs of
    | x :: xs => let
        val y = f (pf | x, env)
        val+ () = (res := cons {b} {0} (y, ?)); val+ cons (_, !p) = res
      in
        aux (pf | xs, f, !p, env); fold@ res
      end
    | nil () => (res := nil ())
  end // end of [aux]
  var res: List b // uninitialized
in
  aux (pf | xs, f, res, env); res
end // end of [list_map_main]

implement list_map_fun<a,b> {n:int} {f:eff} (xs, f) = let
  val f = coerce (f) where {
    extern fun coerce (f: a -<f> b):<> (!unit_v | a, !Ptr) -<f> b
      = "atspre_fun_coerce"
  } // end of [where]
  prval pf = unit_v ()
  val ys = list_map_main (pf | xs, f, null)
  prval unit_v () = pf
in
  ys
end // end of [list_map_fun]

implement list_map_cloptr<a,b> {n:int} {f:eff} (xs, f) = let
  viewtypedef cloptr_t = a -<cloptr,f> b
  fn app (pf: !unit_v | x: a, f: !cloptr_t):<f> b = f (x)
  prval pf = unit_v ()
  val ys = list_map_main<a,b> {unit_v} {cloptr_t} (pf | xs, app, f)
  prval unit_v () = pf
in
  ys
end // end of [list_map_cloptr]

implement list_map_cloref<a,b> {n:int} {f:eff} (xs, f) = let
  viewtypedef cloref_t = a -<cloref,f> b
  fn app (pf: !unit_v | x: a, f: !cloref_t):<f> b = f (x)
  prval pf = unit_v ()
  val ys = list_map_main<a,b> {unit_v} {cloref_t} (pf | xs, app, f)
  prval unit_v () = pf
in
  ys
end // end of [list_map_cloref]

(* ****** ****** *)

implement list_map2_main<a1,a2,b>
  {v:view} {vt:viewtype} {n} {f:eff} (pf | xs, ys, f, env) = let
  var res: List b // uninitialized
  fun aux {n:nat} .<n>. (
      pf: !v
    | xs: list (a1, n)
    , ys: list (a2, n)
    , f: (!v | a1, a2, !vt) -<fun,f> b
    , res: &(List b)? >> list (b, n)
    , env: !vt
  ) :<f> void = begin case+ (xs, ys) of
    | (x :: xs, y :: ys) => let
        val z = f (pf | x, y, env)
        val+ () = (res := cons {b} {0} (z, ?))
        val+ cons (_, !p) = res
      in
        aux (pf | xs, ys, f, !p, env); fold@ res
      end
    | (nil (), nil ()) => (res := nil ())
  end // end of [aux]
in
  aux (pf | xs, ys, f, res, env); res
end // end of [list_map2_main]

implement list_map2_fun<a1,a2,b> {n} {f:eff} (xs, ys, f) = let
  val f = coerce (f) where {
    extern fun coerce
      (f: (a1, a2) -<f> b):<> (!unit_v | a1, a2, !Ptr) -<f> b
      = "atspre_fun_coerce"
  } // end of [where]
  prval pf = unit_v ()
  val zs = list_map2_main (pf | xs, ys, f, null)
  prval unit_v () = pf
in
  zs
end // end of [list_map2_fun]

implement list_map2_cloptr<a1,a2,b> {n} {f:eff} (xs, ys, f) = let
  viewtypedef cloptr_t = (a1, a2) -<cloptr,f> b
  fn app (pf: !unit_v | x: a1, y: a2, f: !cloptr_t):<f> b = f (x, y)
  prval pf = unit_v ()
  val zs = begin
    list_map2_main<a1,a2,b> {unit_v} {cloptr_t} (pf | xs, ys, app, f)
  end
  prval unit_v () = pf
in
  zs
end  // end of [list_map2_cloptr]

(* ****** ****** *)

implement list_reverse_append<a> (xs, ys) = let
  fun aux {n1,n2:nat} .<n1>.
    (xs: list (a, n1), ys: list (a, n2)):<> list (a, n1+n2) =
    case+ xs of x :: xs => aux (xs, x :: ys) | nil () => ys
in
  aux (xs, ys)
end // end of [list_reverse_append]

implement list_reverse xs = list_reverse_append (xs, nil ())

(* ****** ****** *)

implement list_set_elt_at<a> (xs, i, x0) = let
  var res: List a // uninitialized
  fun aux {n,i:nat | i < n} .<n>.
    (xs: list (a, n), i: int i, x0: a, res: &(List a)? >> list (a, n))
    :<> void = let
    val x :: xs = xs
  in
    if i > 0 then let
      val () = (res := cons {a} {0} (x, ?))
      val+ cons (_, !p) = res
    in
      aux (xs, i-1, x0, !p); fold@ res
    end else begin
      res := cons (x0, xs)
    end
  end
in
  aux (xs, i, x0, res); res
end

local

fun{a:t@ype} aux_test {n,i:nat} .<n>.
  (xs: list (a, n), i: int i):<> bool (i < n) = begin
  case+ xs of
  | x :: xs => if i > 0 then aux_test (xs, i-1) else true
  | nil () => false
end // end of [aux_test]

in

implement list_set_elt_at_exn<a> (xs, i, x0) =
  if aux_test<a> (xs, i) then list_set_elt_at (xs, i, x0)
  else $raise ListSubscriptException

implement list_set_elt_at_opt<a> (xs, i, x0) =
  if aux_test<a> (xs, i) then Some_vt (list_set_elt_at (xs, i, x0))
  else None_vt ()

end // end of [local]

(* ****** ****** *)

implement list_split_at<a> {n,i} (xs, i) = let
  var fsts: List a // uninitialized
  fun aux {j:nat | j <= i} .<i-j>.
    (xs: list (a, n-j), ij: int (i-j), fsts: &(List a)? >> list (a, i-j))
    :<> list (a, n-i) =
    if ij > 0 then let
      val+ x :: xs = xs
      val () = (fsts := cons {a} {0} (x, ?)); val+ cons (_, !p) = fsts
      val snds = aux {j+1} (xs, ij - 1, !p)
    in
      fold@ fsts; snds
    end else begin
      fsts := nil (); xs
    end
  val snds = aux {0} (xs, i, fsts)
in
  (fsts, snds)
end // end of [list_split_at]

(* ****** ****** *)

implement list_tail (xs) = let val _ :: xs = xs in xs end
implement list_tail_exn (xs) = case+ xs of
  | _ :: xs => xs | nil () => $raise ListSubscriptException

(* ****** ****** *)

implement list_take<a> (xs, i) = let
  var res: List a // uninitialized
  fun aux {n,i:nat | i <= n} .<i>.
    (xs: list (a, n), i: int i, res: &(List a)? >> list (a, i)):<> void =
    if i > 0 then let
      val x :: xs = xs
      val () = (res := cons {a} {0} (x, ?))
      val+ cons (_, !p) = res
    in
      aux (xs, i-1, !p); fold@ res
    end else begin
      res := nil ()
   end
in
  aux (xs, i, res); res
end

(* ****** ****** *)

implement list_tabulate<a> {n} {f} (f, n) = let
  var res: List a // uninitialized
  fun aux {i:nat | i <= n} .<n-i>.
    (i: int i, f: !natLt n -<f> a, res: &(List a)? >> list (a, n-i)):<f> void =
    if i < n then let
      val () = (res := cons {a} {0} (f i, ?)); val+ cons (_, !p) = res
    in
      aux (i+1, f, !p); fold@ res
    end else begin
      res := nil ()
    end
in
  aux (0, f, res); res
end // end of [list_tabulate]

(* ****** ****** *)

implement list_zip<a,b> (xs, ys) = let
  typedef ab = '(a, b)
  var res: List ab // uninitialized
  fun aux {i:nat} .<i>.
    (xs: list (a, i), ys: list (b, i), res: &(List ab)? >> list (ab, i)):<> void =
    case+ (xs, ys) of
    | (x :: xs, y :: ys) => let
        val () = (res := cons {ab} {0} ('(x, y), ?)); val+ cons (_, !p) = res
      in
        aux (xs, ys, !p); fold@ res
      end
    | (nil (), nil ()) => (res := nil ())
in
  aux (xs, ys, res); res
end

implement list_zip_with<a,b,c> {n} {f:eff} (xs, ys, f) =
  list_map2_cloptr<a,b,c> (xs, ys, f)

(* ****** ****** *)

implement list_unzip<a1,a2> xys = let
  var res1: List a1 and res2: List a2 // uninitialized
  fun aux {n:nat} .<n>. (
      xys: list ('(a1, a2), n)
    , res1: &(List a1)? >> list (a1, n)
    , res2: &(List a2)? >> list (a2, n)
  ) :<> void = begin case+ xys of
    | xy :: xys => let
        val () = (res1 := cons {a1} {0} (xy.0, ?)); val+ cons (_, !p1) = res1
        val () = (res2 := cons {a2} {0} (xy.1, ?)); val+ cons (_, !p2) = res2
      in
        aux (xys, !p1, !p2); fold@ res1; fold@ res2
      end
    | nil () => (res1 := nil (); res2 := nil ())
  end // end of [aux]
in
  aux (xys, res1, res2); (res1, res2)
end

(* ****** ****** *)


// implementing merge sort

(*
 *
 * llist(a, i, n): a list of lists such that
 *   1. the sum of the lengths of lists in the list of lists is i, and
 *   2. the length of the list is n.
 *
 *)

local

//
// this is not an efficient implementation but it is guaranteed to be O(n*lg(n))
//

  datatype llist (a:t@ype+, int, int) =
    | {i,j,n:nat} lcons (a, i+j, n+1) of (list (a, i), llist (a, j, n))
    | lnil (a, 0, 0)

  typedef lte (a:t@ype, env: viewtype, f:eff) = (a, a, !env) -<fun,f> bool

  fun{a:t@ype} aux1
    {env:viewtype} {i:nat} {f:eff} .<i>.
    (lte: lte (a, env, f), xs: list (a, i), env: !env)
    :<f> [n:nat] llist (a, i, n) = case+ xs of
    | x1 :: x2 :: xs => let
        val l: list (a, 2) =
          if lte (x1, x2, env) then x1 :: x2 :: nil else x2 :: x1 :: nil
      in
         lcons (l, aux1 (lte, xs, env))
      end
    | l as '[x] => lcons (l, lnil ())
    | nil () => lnil

  fun{a:t@ype} aux2
    {env:viewtype} {i,j:nat} {f:eff} .<i+j>. (
      lte: lte (a, env, f), xs: list (a, i), ys: list (a, j), env: !env
    ) :<f> list (a, i+j) = begin
    case+ (xs, ys) of
    | (xs as x :: xs', ys as y :: ys') => begin
        if lte (x, y, env) then begin
          x :: aux2 (lte, xs', ys, env)
        end else begin
          y :: aux2 (lte, xs, ys', env)
        end
      end
    | (xs, nil ()) => xs
    | (nil (), ys) => ys
  end // end of [aux2]

  fun{a:t@ype} aux3
    {env:viewtype} {i,n:nat} {f:eff} .<n>.
    (lte: lte (a, env, f), xss: llist (a, i, n), env: !env)
    :<f> [n1:nat | (n < 2 && n1 == n) || n1 < n] llist (a, i, n1) =
    case+ xss of
    | lcons (xs1, lcons (xs2, xss)) => begin
        lcons (aux2 (lte, xs1, xs2, env), aux3 (lte, xss, env))
      end
    | _ =>> xss

  fun{a:t@ype} aux4
    {env:viewtype} {i,n:nat} {f:eff} .<n>.
    (lte: lte (a, env, f), xss: llist (a, i, n), env: !env)
    :<f> list (a, i) = begin case+ xss of
    | lnil () => nil ()
    | lcons (xs, lnil ()) => xs
    | _ =>> begin
        aux4 (lte, aux3 (lte, xss, env), env)
      end
  end // end of [aux4]

in

implement list_mergesort (xs, lte, env) = aux4 (lte, aux1 (lte, xs, env), env)

end // end of [local]

(* ****** ****** *)

// implementing quick sort

local

//
// this may not be a practical implementation as it can easily be O(n*n)
//

  typedef lte (a:t@ype, env: viewtype, f:eff) = (a, a, !env) -<fun,f> bool

  fun{a:t@ype} qs {env:viewtype} {n:nat} {f:eff} .<n,0>.
    (lte: lte (a, env, f), xs: list (a, n), env: !env)
    :<f> list (a, n) = begin
    case+ xs of // [case+]: exhaustive pattern matching
    | x' :: xs' => begin
        part {env} {n-1,0,0} (lte, x', xs', nil, nil, env)
      end
    | nil () => nil ()
  end // end of [qs]

  and part {env:viewtype} {p,l,r:nat} {f:eff} .<p+l+r,p+1>. (
      lte: lte (a, env, f)
    , x: a, xs: list (a, p)
    , l: list (a, l), r: list (a, r)
    , env: !env
    ) :<f> list (a, p+l+r+1) = begin
    case+ xs of // case+ mandates exhaustive pattern matching
    | x' :: xs' => begin
        if lte (x', x, env) then begin
          part {env} {p-1,l+1,r} (lte, x, xs', x' :: l, r, env)
        end else begin
          part {env} {p-1,l,r+1} (lte, x, xs', l, x' :: r, env)
        end
      end // end of [::]
    | nil () => begin
        list_append (qs (lte, l, env), x :: qs (lte, r, env))
      end // end of [nil]
  end // end of [part]
in

implement list_quicksort (xs, lte, env) = qs (lte, xs, env)

end // end of [local]

(* ****** ****** *)

(* end of [list.dats] *)
