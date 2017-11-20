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

implement mul_is_fun (pf1, pf2) =
  let
     prfun aux {m:nat;n:int} {p1,p2:int} .<m>.
        (pf1: MUL (m, n, p1), pf2: MUL (m, n, p2)): [p1==p2] void =
       case+ (pf1, pf2) of
         | (MULbas (), MULbas ()) => ()
         | (MULind pf1, MULind pf2) => aux (pf1, pf2)
  in
     case+ (pf1, pf2) of
       | (MULneg pf1, MULneg pf2) => aux (pf1, pf2)
       | (_, _) =>> aux (pf1, pf2)
  end

implement mul_nat_nat_nat (pf) = let
prfun aux {m,n:nat} {p:int} .<m>. (pf: MUL (m, n,p)): [p>=0] void =
  case+ pf of MULbas () => () | MULind pf => aux pf
in
  aux pf
end // end of [mul_nat_nat_nat]

implement mul_m_0_0 () = let
prfun aux {m:int} .<max(2 * m, 2 * (~m) + 1)>. (): MUL (m, 0, 0) =
  sif m > 0 then MULind (aux {m-1} ())
  else sif m < 0 then MULneg (aux {~m} ())
  else MULbas ()
in
  aux ()
end // end of [mul_m_0_0]

implement mul_negate (pf) = let
prfn aux {m,n,p:int} (pf: MUL (m, n, p)): MUL (~m, n, ~p) =
  sif m > 0 then MULneg pf
  else sif m < 0 then
    let prval MULneg pf = pf in pf end
  else
    let prval MULbas () = pf in pf end
in
  aux (pf)
end // end of [mul_negate]

prfun mul_m_n1_mnm {m,n:int} {p:int} .<max(2*m, 2*(~m)+1)>.
  (pf: MUL (m, n, p)): MUL (m, n+1, p+m) =
  case+ pf of
    | MULbas () => MULbas ()
    | MULind pf => MULind (mul_m_n1_mnm pf)
    | MULneg pf => MULneg (mul_m_n1_mnm pf) 

prfun mul_m_neg_n_neg_mn {m,n:int} {p:int} .<max(2*m, 2*(~m)+1)>.
  (pf: MUL (m, n, p)): MUL (m, ~n, ~p) =
  case+ pf of
    | MULbas () => MULbas ()
    | MULind pf => MULind (mul_m_neg_n_neg_mn pf)
    | MULneg pf => MULneg (mul_m_neg_n_neg_mn pf) 

//

implement mul_commute (pf) =
  let
     prfun aux {m,n:int} {p:int} .<max(2*m, 2*(~m)+1)>.
       (pf: MUL (m, n, p)): MUL (n, m, p) =
       case+ pf of
         | MULbas () => mul_m_0_0 {n} ()
         | MULind pf => mul_m_n1_mnm (aux pf)
         | MULneg pf => mul_m_neg_n_neg_mn (aux pf)
  in
     aux pf     
  end

//

implement mul_distribute (pf1, pf2) =
  let
     prfun aux {m,n1,n2:int} {p1,p2:int} .<max(2*m, 2*(~m)+1)>.
       (pf1: MUL (m, n1, p1), pf2: MUL (m, n2, p2)): MUL (m, n1+n2, p1+p2) =
       case+ (pf1, pf2) of
         | (MULbas (), MULbas ()) => MULbas ()
         | (MULind pf1, MULind pf2) => MULind (aux (pf1, pf2))
         | (MULneg pf1, MULneg pf2) => MULneg (aux (pf1, pf2))
  in
     aux (pf1, pf2)
  end

//

(*

implement mul_with_cst #{i} #{m,n} (pf0) =
  let
     prval pf0' = mul_commute pf0
     prval pf1 = mul_make {i,n} ()
     prval pf1' = mul_commute pf1
     prval pf' = mul_distribute (pf0', pf1')
     prval () = mul_elim pf1
  in
     mul_commute pf'
  end

*)

(* ****** ****** *)

(* greatest common divisors *)

local

prfun aux1 {m,n:pos} {r:int} .<m+n>.
  (pf: GCD (m, n, r)): GCD (n, m, r) =
  sif m <= n then
    let prval GCDind1 pf1 = pf in
       sif m < n then GCDind2 (aux1 pf1) else pf
    end
  else
    let prval GCDind2 pf1 = pf in
       GCDind1 (aux1 pf1)
    end

prfn aux2 {m:nat;n:int} {r:int} 
  (pf: GCD (m, n, r)): GCD (n, m, r) =
  sif n > 0 then
     sif m > 0 then aux1 pf else
        let prval GCDbas2 () = pf in GCDbas1 () end
  else sif n < 0 then
    let prval GCDneg1 pf1 = pf in
       sif m > 0 then GCDneg2 (aux1 pf1) else
          let prval GCDbas2 () = pf1 in GCDneg2 (GCDbas1 ()) end
    end
  else
    let prval GCDbas1 () = pf in
       sif m > 0 then GCDbas2 () else pf
    end

in

// gcd_commute: GCD (m, n, r) -> GCD (n, m, r)
implement gcd_commute {m,n} (pf) =
  sif m >= 0 then aux2 pf else
     let prval GCDneg2 pf1 = pf in
        sif n >= 0 then GCDneg1 (aux2 pf1) else
           let prval GCDneg2 pf2 = aux2 pf1 in
              GCDneg2 (GCDneg1 pf2)
           end
     end

end // end of local

(* ****** ****** *)

(* end of [arith.dats] *)
