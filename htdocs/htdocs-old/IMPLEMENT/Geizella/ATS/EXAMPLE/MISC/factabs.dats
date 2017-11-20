
#if ABSINT = 0 #then

abst@ype absint

typedef T = absint

extern val zero : T and one : T

extern fun add (x1: T, x2: T): T
overload + with add

extern fun sub (x1: T, x2: T): T
overload - with sub

extern fun mul (x1: T, x2: T): T
overload * with mul

extern fun gt (x1: T, x2: T): bool
overload > with gt

extern fun gte (x1: T, x2: T): bool
overload >= with gte

extern fun lt (x1: T, x2: T): bool
overload < with lt

extern fun lte (x1: T, x2: T): bool
overload <= with lte

extern fun eq (x1: T, x2: T): bool
overload = with eq

extern fun neq (x1: T, x2: T): bool
overload <> with neq

extern fun ofstring_absint (s: string): T
overload ofstring with ofstring_absint

extern fun print_absint (x: T): void
overload print with print_absint

#endif

fun fact (x: T): T =
  if x > zero then x * fact (x - one) else one

(* ****** ****** *)

(* end of [factabs.dats] *)
