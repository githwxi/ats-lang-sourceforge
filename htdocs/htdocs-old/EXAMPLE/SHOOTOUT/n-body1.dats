(*
** The Great Computer Language Shootout
** http://shootout.alioth.debian.org/
**
** contributed by Hongwei Xi (hwxi AT cs DOT bu DOT edu)
**
** compilation command:
**   atscc -msse2 -mfpmath=sse -O3 n-body.dats -o n-body -lm
*)

staload _(*anonymous*) = "prelude/DATS/array.dats"

staload M = "libc/SATS/math.sats"

typedef body = (
  double, double, double, double, double, double, double
)

val sun = (0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 1.0)

val jupiter = (
  4.84143144246472090,
 ~1.16032004402742839,
 ~1.03622044471123109e-1,
  1.66007664274403694e-3,
  7.69901118419740425e-3,
 ~6.90460016972063023e-5,
  9.54791938424326609e-4
)

val saturn = (
  8.34336671824457987,
  4.12479856412430479,
 ~4.03523417114321381e-1,
 ~2.76742510726862411e-3,
  4.99852801234917238e-3,
  2.30417297573763929e-5,
  2.85885980666130812e-4
)

val neptune = (
  1.28943695621391310e+1,
 ~1.51111514016986312e+1,
 ~2.23307578892655734e-1,
  2.96460137564761618e-3,
  2.37847173959480950e-3,
 ~2.96589568540237556e-5,
  4.36624404335156298e-5
)

val uranus = (
  1.53796971148509165e+1,
 ~2.59193146099879641e+1,
  1.79258772950371181e-1,
  2.68067772490389322e-3,
  1.62824170038242295e-3,
 ~9.51592254519715870e-5,
  5.15138902046611451e-5
)

#define PI 3.1415926535898
#define SOLAR_MASS (4.0 * PI * PI)
#define DAYS_PER_YEAR 365.24

typedef bodylst (n: int) = list (body, n)

#define N 5; #define N1 (N - 1)

macdef darray () = array_make_elt<double> (N, 0.0)
val (x, y, z) = (darray (), darray (), darray ())
val (vx, vy, vz) = (darray (), darray (), darray ())
val m = darray ()

val () = loop (0, theBodies) where {
  #define DPY DAYS_PER_YEAR
  val theBodies = '[sun, jupiter, saturn, neptune, uranus]
  fun loop {i: nat} (i: int i, bs: bodylst (N-i)): void =
    if i < N then let
      val+ list_cons (b, bs) = bs
    in
      x[i] := b.0; y[i] := b.1; z[i] := b.2;
      vx[i] := b.3 * DPY; vy[i] := b.4 * DPY; vz[i] := b.5 * DPY;
      m[i] := b.6 * SOLAR_MASS;
      loop (i+1, bs)
    end
}

(* one step *)

infix 0 += -=  // for similar C notation
macdef += (x, d) = (,(x) := ,(x) + ,(d))
macdef -= (x, d) = (,(x) := ,(x) - ,(d))

fn advance (dt: double): void = let
  fun pl {i:nat | i <= N } (dt: double, i: int i): void =
    if i < N then begin
      x[i] += dt*vx[i]; y[i] += dt*vy[i]; z[i] += dt*vz[i]; pl (dt, i+1)
    end
  fun vl {i,j:int | 0 <= i; i < j; j <= N}
    (dt: double, i: int i, j: int j): void = case+ 0 of
    | _ when i < N1 => if j < N then let
        val dx = x[i] - x[j] and dy = y[i] - y[j] and dz = z[i] - z[j]
        val dist2 = dx * dx + dy * dy + dz * dz
        val dist = $M.sqrt (dist2); val mag = dt / (dist * dist2)
        val mi = m[i] * mag and mj = m[j] * mag
      in
        vx[i] -= dx * mj; vy[i] -= dy * mj; vz[i] -= dz * mj; 
        vx[j] += dx * mi; vy[j] += dy * mi; vz[j] += dz * mi;
        vl (dt, i, j+1)
      end else vl (dt, i+1, i+2)
    | _ => pl (dt, 0)
in
  vl (dt, 0, 1)
end

(* calculate initial velocity for the sun *)
fn offmoment (): void = let
  #define M SOLAR_MASS
  fun loop (i: natLte N, px: double, py: double, pz: double): void =
    if i < N then let
      val mi = m[i] in loop (i+1, px+vx[i]*mi, py+vy[i]*mi, pz+vz[i]*mi)
    end else begin
      vx[0] := ~px / M; vy[0] := ~py / M; vz[0] := ~pz / M
    end // end of [if]
in
  loop (1, 0.0, 0.0, 0.0)
end

fn energy (): double = let // mutual recursion
  fn* l (i: natLt N, j: natLte N, e: double): double =
    if j < N then let
      val dx = x[i] - x[j] and dy = y[i] - y[j] and dz = z[i] - z[j]
      val dist2 = dx * dx + dy * dy + dz * dz; val dist = $M.sqrt (dist2)
    in
      l (i, j+1, e-m[i]*m[j]/dist)
    end else l0 (i+1, e)

  and l0 (i: natLte N, e: double): double =
    if i < N then let
      val vxi = vx[i] and vyi = vy[i] and vzi = vz[i]
    in
      l (i, i+1, e + 0.5*m[i]*(vxi*vxi+vyi*vyi+vzi*vzi))
    end else e
in
  l0 (0, 0.0)
end

fun advances (i: Nat): void = if i > 0 then (advance 0.01; advances (i-1))

implement main (argc, argv) = let
  val () = assert (argc = 2)
  val n = int1_of (argv.[1]); val () = assert (n >= 2)
in
  offmoment();
  printf ("%.9f\n", @(energy()));
  advances n;
  printf ("%.9f\n", @(energy()));
end

(* end of [n-body1.dats] *)
