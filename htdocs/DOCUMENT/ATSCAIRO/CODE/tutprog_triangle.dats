(*
**
** ATS/Cairo Tutorial: drawing triangles
**
** Author: Hongwei Xi (hwxi AT cs DOT bu DOT edu)
** Time: 2010-04
**
*)

(*
** Copyright (C) 2009-2010 Hongwei Xi, Boston University
**
** Permission is hereby granted, free of charge, to any person
** obtaining a copy of this software and associated documentation
** files (the "Software"), to deal in the Software without
** restriction, including without limitation the rights to use,
** copy, modify, merge, publish, distribute, sublicense, and/or sell
** copies of the Software, and to permit persons to whom the
** Software is furnished to do so, subject to the following
** conditions:
**
** The above copyright notice and this permission notice shall be
** included in all copies or substantial portions of the Software.
**
** THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
** EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
** OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
** NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT
** HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
** WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
** FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
** OTHER DEALINGS IN THE SOFTWARE.
*)

(* ****** ****** *)
//
// How to compile:
//   atscc -o $@ tutprog_triangle.dats `pkg-config gtk+-2.0 --cflags --libs`
//
// How to test:
//   ./tutprog_triangle
//
(* ****** ****** *)

staload "libc/SATS/random.sats"
staload "contrib/cairo/SATS/cairo.sats"

(* ****** ****** *)

fun draw_triangle {l:agz} (
    cr: !cairo_ref l
  , x0: double, y0: double, x1: double, y1: double, x2: double, y2: double
  ) : void = () where {
  val () = cairo_move_to (cr, x0, y0)
  val () = cairo_line_to (cr, x1, y1)
  val () = cairo_line_to (cr, x2, y2)
  val () = cairo_close_path (cr)
} // end of [draw_triangle]

(* ****** ****** *)

typedef triangle = @{
  r= double, g= double, b= double
, x0= double, y0= double, x1= double, y1= double, x2= double, y2= double
} // end of [triangle]

local

var tri: triangle = @{
  r=0.0, g=1.0, b=0.0
, x0= 0.0, y0= 1.0, x1= 0.5, y1= 0.0, x2= 1.0, y2= 1.0
} // end of [var]

in

val p_tri = &tri
val (pf_tri | ()) =
  vbox_make_view_ptr {triangle} (view@ tri | &tri)
// end of [pf_theTriangle]

end // end of [local]

(* ****** ****** *)

staload "contrib/glib/SATS/glib.sats"
staload "contrib/glib/SATS/glib-object.sats"

(* ****** ****** *)

staload "contrib/GTK/SATS/gdk.sats"
staload "contrib/GTK/SATS/gtk.sats"
staload "contrib/GTK/SATS/gtkclassdec.sats"

(* ****** ****** *)

%{^
GtkWidget *the_drawingarea = NULL;
ats_ptr_type
the_drawingarea_get () {
  g_object_ref (G_OBJECT(the_drawingarea)); return the_drawingarea ;
}
ats_void_type
the_drawingarea_initset (ats_ptr_type x) {
  g_object_ref(G_OBJECT(x)) ;
  if (the_drawingarea) g_object_unref (G_OBJECT(the_drawingarea));
  the_drawingarea = x ;
  return ;
} // end of [the_drawingarea_initset]
%} // end of [%{^] 
extern
fun the_drawingarea_get
  (): GtkDrawingArea_ref1 = "the_drawingarea_get"
// end of [the_drawingarea_get]
extern
fun the_drawingarea_initset
  (x: !GtkDrawingArea_ref1): void = "the_drawingarea_initset"
// end of [the_drawingarea_initset]

(* ****** ****** *)

staload RAND = "libc/SATS/random.sats"

fun fnext () = () where {
  val r = $RAND.drand48 ()
  and g = $RAND.drand48 ()
  and b = $RAND.drand48 ()
  val x0 = $RAND.drand48 ()
  val y0 = $RAND.drand48 ()
  val x1 = $RAND.drand48 ()
  val y1 = $RAND.drand48 ()
  val x2 = $RAND.drand48 ()
  val y2 = $RAND.drand48 ()
  val () = () where {
    prval vbox pf = pf_tri
    val () = p_tri->r := r
    val () = p_tri->g := g
    val () = p_tri->b := b
    val () = p_tri->x0 := x0
    val () = p_tri->y0 := y0
    val () = p_tri->x1 := x1
    val () = p_tri->y1 := y1
    val () = p_tri->x2 := x2
    val () = p_tri->y2 := y2
  } // end of [val]
  val darea = the_drawingarea_get ()
  val (pf, fpf | p) = gtk_widget_getref_allocation (darea)
  val () = gtk_widget_queue_draw_area (darea, (gint)0, (gint)0, p->width, p->height)
  prval () = minus_addback (fpf, pf | darea)
  val () = g_object_unref (darea)
} // end of [fnext]

fun draw_main {l:agz} (
    cr: !cairo_ref l, W: int, H: int
  ) : void = () where {
  val W = (double_of)W and H = (double_of)H
(*
  val () = (print "W = "; print W; print_newline ())
  val () = (print "H = "; print H; print_newline ())
*)
  var r: double
  and g: double
  and b: double
  var x0: double and y0: double
  var x1: double and y1: double
  var x2: double and y2: double
  val () = () where {
    prval vbox pf = pf_tri
    val () = r := p_tri->r
    val () = g := p_tri->g
    val () = b := p_tri->b
    val () = x0 := p_tri->x0 and () = y0 := p_tri->y0
    val () = x1 := p_tri->x1 and () = y1 := p_tri->y1
    val () = x2 := p_tri->x2 and () = y2 := p_tri->y2
  } // end of [val]
  val () = draw_triangle (cr, W*x0, H*y0, W*x1, H*y1, W*x2, H*y2)
  val () = cairo_set_source_rgb (cr, r, g, b)
  val () = cairo_fill_preserve (cr)
  val () = cairo_set_line_width (cr, 2.5)
  val () = cairo_set_source_rgb (cr, 1-r, 1-g, 1-b)
  val () = cairo_stroke (cr)
} // end of [draw_main]

(* ****** ****** *)

%{^
extern
ats_void_type
mainats (ats_int_type argc, ats_ptr_type argv) ;
%}

(* ****** ****** *)

fun on_expose_event {l:agz} (
  darea: !GtkDrawingArea_ref l, event: &GdkEvent
) : gboolean = let
  val (fpf_win | win) = gtk_widget_get_window (darea)
  val () = assert_errmsg (g_object_isnot_null (win), #LOCATION)
  val cr = gdk_cairo_create (win)
  prval () = minus_addback (fpf_win, win | darea)
  val (pf, fpf | p) = gtk_widget_getref_allocation (darea)
  val () = draw_main (cr, (int_of)p->width, (int_of)p->height)
  prval () = minus_addback (fpf, pf | darea)
  val () = cairo_destroy (cr)
in
  GTRUE // HX: the event is properly handled
end // end of [on_expose_event]

(* ****** ****** *)

macdef gs = gstring_of_string

extern fun main1 (): void = "main1"

implement main1 () = () where {
  val window = gtk_window_new (GTK_WINDOW_TOPLEVEL)
  val () = gtk_window_set_default_size (window, (gint)400, (gint)400)
  val (fpf_x | x) = (gs)"cairo: random triangles"
  val () = gtk_window_set_title (window, x)
  prval () = fpf_x (x)
  val _sid = g_signal_connect
    (window, (gsignal)"delete-event", G_CALLBACK (gtk_widget_destroy), (gpointer)null)
  val _sid = g_signal_connect
    (window, (gsignal)"destroy", G_CALLBACK (gtk_main_quit), (gpointer)null)
//
  val vbox0 = gtk_vbox_new (GFALSE(*homo*), (gint)10(*spacing*))
  val () = gtk_container_add (window, vbox0)
  val darea = gtk_drawing_area_new ()
  val () = the_drawingarea_initset (darea)
  val () = gtk_box_pack_start (vbox0, darea, GTRUE, GTRUE, (guint)0)
  val _sid = g_signal_connect
    (darea, (gsignal)"expose-event", G_CALLBACK (on_expose_event), (gpointer)null)
  val () = g_object_unref (darea)
//
  val hsep = gtk_hseparator_new ()
  val () = gtk_box_pack_start (vbox0, hsep, GFALSE, GTRUE, (guint)0)
  val () = g_object_unref (hsep)
//
  val hbox1 = gtk_hbox_new (GFALSE(*homo*), (gint)5(*spacing*))
  val () = gtk_box_pack_start (vbox0, hbox1, GFALSE, GTRUE, (guint)10)
  val (fpf_x | x) = (gs)"_Next"
  val btn_next = gtk_button_new_with_mnemonic (x)
  prval () = fpf_x (x)
  val _sid = g_signal_connect
    (btn_next, (gsignal)"clicked", G_CALLBACK(fnext), (gpointer)null)
  // end of [val]
  val () = gtk_box_pack_start (hbox1, btn_next, GTRUE, GTRUE, (guint)10)
  val () = g_object_unref (btn_next)
  val (fpf_x | x) = (gs)"_Close"
  val btn_close = gtk_button_new_with_mnemonic (x)
  prval () = fpf_x (x)
  val _sid = g_signal_connect
    (btn_close, (gsignal)"clicked", G_CALLBACK(gtk_main_quit), (gpointer_vt)window)
  // end of [val]
  val () = gtk_box_pack_start (hbox1, btn_close, GTRUE, GTRUE, (guint)10)
  val () = g_object_unref (btn_close)
  val () = g_object_unref (hbox1)
//
  val () = g_object_unref (vbox0)
  val () = gtk_widget_show_all (window)
  val () = g_object_unref (window)
  val () = $RAND.srand48_with_time ()
  val () = gtk_main ()
} // end of [val]

(* ****** ****** *)

implement main_dummy () = ()

(* ****** ****** *)

%{$
ats_void_type
mainats (
  ats_int_type argc, ats_ptr_type argv
) {
  gtk_init ((int*)&argc, (char***)&argv) ;
  main1 () ;
  return ;
} // end of [mainats]
%} // end of [%{$]

(* ****** ****** *)

(* end of [tutprog_triangle.dats] *)
