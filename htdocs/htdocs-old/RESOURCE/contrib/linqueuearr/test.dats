(*

// author: Hongwei Xi (October, 2008)

*)

(* ****** ****** *)

//

staload LQA = "linqueuearr.dats"
staload QAR = "queuearr_ref.dats"
staload QAM = "queuearr_mut.dats"

//

val () = (print "test: linear queue:"; print_newline ())

var xs = $LQA.linqueuearr_make<double> (2)

val () = $LQA.linqueuearr_enqueue<double> (xs, 1.0)
val () = $LQA.linqueuearr_enqueue<double> (xs, 2.0)

val x1 = $LQA.linqueuearr_dequeue<double> (xs)
val () = (print "x1 = "; print x1; print_newline ())
val x2 = $LQA.linqueuearr_dequeue<double> (xs)
val () = (print "x2 = "; print x2; print_newline ())

val () = $LQA.linqueuearr_enqueue<double> (xs, 3.0)
val () = $LQA.linqueuearr_enqueue<double> (xs, 4.0)

val x3 = $LQA.linqueuearr_dequeue<double> (xs)
val () = (print "x3 = "; print x3; print_newline ())

val () = $LQA.linqueuearr_enqueue<double> (xs, 5.0)

val x4 = $LQA.linqueuearr_dequeue<double> (xs)
val () = (print "x4 = "; print x4; print_newline ())
val x5 = $LQA.linqueuearr_dequeue<double> (xs)
val () = (print "x5 = "; print x5; print_newline ())

//

val () = (print "test: persistent queue:"; print_newline ())

var xs = $QAR.queuearr_ref_make<double> (3)

val () = $QAR.queuearr_ref_enqueue_exn<double> (xs, 1.0)
val () = $QAR.queuearr_ref_enqueue_exn<double> (xs, 2.0)

val x1 = $QAR.queuearr_ref_dequeue_exn<double> (xs)
val () = (print "x1 = "; print x1; print_newline ())
val x2 = $QAR.queuearr_ref_dequeue_exn<double> (xs)
val () = (print "x2 = "; print x2; print_newline ())

val () = $QAR.queuearr_ref_enqueue_exn<double> (xs, 3.0)
val () = $QAR.queuearr_ref_enqueue_exn<double> (xs, 4.0)
val () = $QAR.queuearr_ref_enqueue_exn<double> (xs, 5.0)

val x3 = $QAR.queuearr_ref_dequeue_exn<double> (xs)
val () = (print "x3 = "; print x3; print_newline ())
val x4 = $QAR.queuearr_ref_dequeue_exn<double> (xs)
val () = (print "x4 = "; print x4; print_newline ())
val x5 = $QAR.queuearr_ref_dequeue_exn<double> (xs)
val () = (print "x5 = "; print x5; print_newline ())

//

val () = (print "test: multithread queue:"; print_newline ())

var xs = $QAM.queuearr_mut_make<double> (3)

val () = (print "test: queue is created."; print_newline ())

val () = $QAM.queuearr_mut_enqueue<double> (xs, 1.0)
val () = $QAM.queuearr_mut_enqueue<double> (xs, 2.0)

val x1 = $QAM.queuearr_mut_dequeue<double> (xs)
val () = (print "x1 = "; print x1; print_newline ())
val x2 = $QAM.queuearr_mut_dequeue<double> (xs)
val () = (print "x2 = "; print x2; print_newline ())

val () = $QAM.queuearr_mut_enqueue<double> (xs, 3.0)
val () = $QAM.queuearr_mut_enqueue<double> (xs, 4.0)
val () = $QAM.queuearr_mut_enqueue<double> (xs, 5.0)

val x3 = $QAM.queuearr_mut_dequeue<double> (xs)
val () = (print "x3 = "; print x3; print_newline ())
val x4 = $QAM.queuearr_mut_dequeue<double> (xs)
val () = (print "x4 = "; print x4; print_newline ())
val x5 = $QAM.queuearr_mut_dequeue<double> (xs)
val () = (print "x5 = "; print x5; print_newline ())

(* ****** ****** *)

implement main () = ()

(* ****** ****** *)

(* end of [test.dats] *)
