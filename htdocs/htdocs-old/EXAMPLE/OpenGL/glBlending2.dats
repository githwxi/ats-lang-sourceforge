%{^

extern ats_void_type mainats (ats_int_type argc, ats_ptr_type argv) ;

%}

staload "libc/GL/SATS/gl.sats"
staload "libc/GL/SATS/glut.sats"

(* ****** ****** *)

#define MAXZ  2.0
#define MINZ ~2.0
#define ZINC  0.001

staload _(*anonymous*) = "prelude/DATS/reference.dats"

val solidZ = ref_make_elt<double> (MAXZ)
val transparentZ = ref_make_elt<double> (MINZ)

(* ****** ****** *)

#include "glList.dats"

(* ****** ****** *)

val cubeLst_ref = glListRef_make ()
val sphereLst_ref = glListRef_make ()

extern fun initialize (): void = "initialize"
implement initialize () = let
  val (pf1_gc, pf1 | p_mat_specular, _(*4*)) = @[float][1.0, 1.0, 1.0, 0.15]
  val (pf2_gc, pf2 | p_mat_shininess, _(*1*)) = @[float][100.0]
  val (pf3_gc, pf3 | p_position, _(*4*)) = @[float][0.5, 0.5, 1.0, 0.0]
(*
  val () = glMaterialfv (pf1 | GL_FRONT, GL_SPECULAR, p_mat_specular)
  val () = glMaterialfv (pf2 | GL_FRONT, GL_SHININESS, p_mat_shininess)
  val () = glLightfv (pf3 | GL_LIGHT0, GL_POSITION, p_position)
*)
  val () = glEnable (GL_LIGHTING)
  val () = glEnable (GL_LIGHT0)
  val () = glEnable (GL_DEPTH_TEST)

  val (pf_sphereLst | sphereLst) = glGenList_exn ()
  val (pf_list | ()) = glNewList (pf_sphereLst | sphereLst, GL_COMPILE)
  val () = glutSolidSphere (0.4, 20, 16)
  val () = glEndList (pf_list | (*none*))
  val () = glListRef_set (pf_sphereLst | sphereLst_ref, sphereLst)

  val (pf_cubeLst | cubeLst) = glGenList_exn ()
  val (pf_list | ()) = glNewList (pf_cubeLst | cubeLst, GL_COMPILE)
  val () = glutSolidCube (0.6)
  val () = glEndList (pf_list | (*none*))
  val () = glListRef_set (pf_cubeLst | cubeLst_ref, cubeLst)

  val () = array_ptr_free {float} (pf1_gc, pf1 | p_mat_specular)
  val () = array_ptr_free {float} (pf2_gc, pf2 | p_mat_shininess)
  val () = array_ptr_free {float} (pf3_gc, pf3 | p_position)
in
  // empty
end // end of [initialize]

(* ****** ****** *)

local

typedef GLfloat = float

in

extern fun glLightfv {n:nat} {l:addr}
  (pf: !array_v (GLfloat, n, l) | light: GLenum, pname: GLenum, p: ptr l): void
  = "atslib_glLightfv"

extern fun glLightModelfv {n:nat} {l:addr}
  (pf: !array_v (GLfloat, n, l) | pname: GLenum, params: ptr l): void
  = "atslib_glLightModelfv"

extern fun glMaterialfv {n:nat} {l:addr}
  (pf: !array_v (GLfloat, n, l) | face: GLenum, pname: GLenum, params: ptr l): void
  = "atslib_glMaterialfv"

end

extern fun display (): void = "display"
implement display () = let
  val (pf1_gc, pf1 | p_mat_solid, _(*4*)) = @[float][0.75, 0.75, 0.0, 1.0]
  val (pf2_gc, pf2 | p_mat_zero, _(*4*)) = @[float][0.0, 0.0, 0.0, 1.0]
  val (pf3_gc, pf3 | p_transparent, _(*4*)) = @[float][0.0, 0.8, 0.8, 0.6]
  val (pf4_gc, pf4 | p_emission, _(*4*)) = @[float][0.0, 0.3, 0.3, 0.6]

  val () = glClear (GL_COLOR_BUFFER_BIT lor GL_DEPTH_BUFFER_BIT)

  val (pf_push | ()) = glPushMatrix ()
  val () = glTranslatef (~0.15, ~0.15, !solidZ)
  val () = glMaterialfv (pf2 | GL_FRONT, GL_EMISSION, p_mat_zero)
  val () = glMaterialfv (pf1 | GL_FRONT, GL_DIFFUSE, p_mat_solid)
  val () = glCallListRef (sphereLst_ref)
  val () = glPopMatrix (pf_push | (*none*))
  val () = array_ptr_free {float} (pf1_gc, pf1 | p_mat_solid)
  val () = array_ptr_free {float} (pf2_gc, pf2 | p_mat_zero)

  val (pf_push | ()) = glPushMatrix ()
  val () = glTranslatef (0.15, 0.15, !transparentZ)
  val () = glRotatef (15.0, 1.0, 1.0, 0.0)
  val () = glRotatef (30.0, 0.0, 1.0, 0.0)
  val () = glMaterialfv (pf4 | GL_FRONT, GL_EMISSION, p_emission)
  val () = glMaterialfv (pf3 | GL_FRONT, GL_DIFFUSE, p_transparent)
  val () = glEnable (GL_BLEND)
  val () = glDepthMask (GL_FALSE)
  val () = glBlendFunc (GL_SRC_ALPHA, GL_ONE)
  val () = glCallListRef (cubeLst_ref)
  val () = glDepthMask (GL_TRUE)
  val () = glDisable (GL_BLEND)
  val () = glPopMatrix (pf_push | (*none*))
  val () = array_ptr_free {float} (pf3_gc, pf3 | p_transparent)
  val () = array_ptr_free {float} (pf4_gc, pf4 | p_emission)

in
  glutSwapBuffers ()
end // end of [display]

(* ****** ****** *)

extern fun animate (): void = "animate"
implement animate () = let
  val solidZ_v = !solidZ
  val transparentZ_v = !transparentZ
in
  if solidZ_v <= MINZ then glutIdleFuncNull ()
  else if transparentZ_v >= MAXZ then glutIdleFuncNull ()
  else let
    val () = !solidZ := solidZ_v - ZINC
    val () = !transparentZ := transparentZ_v + ZINC
  in
    glutPostRedisplay ()
  end
end // end of [animate]

(* ****** ****** *)

extern fun reshape (w: int, h: int): void = "reshape"
implement reshape (w, h) = let
  val () = glViewport (0, 0, w, h)
  val () = glMatrixMode (GL_PROJECTION)
  val () = glLoadIdentity ()
  val () = case+ 0 of
    | _ when (w <= h) => let
        val hw = (double_of h) / (double_of w)
      in
        glOrtho (~1.5, 1.5, ~1.5 * hw, 1.5 * hw, ~10.0, 10.0)
      end
    | _ (* w > h *) => let
        val wh = (double_of w) / (double_of h)
      in
        glOrtho (~1.5 * wh, 1.5 * wh, ~1.5, 1.5, ~10.0, 10.0)
      end
  val () = glMatrixMode (GL_MODELVIEW)
  val () = glLoadIdentity ()
in
  // empty
end // end of [reshape]

(* ****** ****** *)

%{^

ats_char_type char_of_uchar (ats_uchar_type c) { return c ; }

%}

extern fun char_of_uchar (c: uchar): char = "char_of_uchar"

//

extern fun keyboard (key: uchar, x: int, y: int): void = "keyboard"
implement keyboard (key, x, y) = let
  val key = char_of_uchar (key)
in
  case+ 0 of
  | _ when (key = 'a' orelse key = 'A') => begin
      !solidZ := MAXZ; !transparentZ := MINZ; glutIdleFunc (animate)
    end
  | _ when (key = 'r' orelse key = 'R') => begin
      !solidZ := MAXZ; !transparentZ := MINZ; glutPostRedisplay ()
    end
  | _ when (key = '\033') => exit (0)
  | _ => ()
end // end of [keyboard]

(* ****** ****** *)

implement main_dummy () = ()

(* ****** ****** *)

%{$

ats_void_type mainats
  (ats_int_type argc, ats_ptr_type argv) {
  glutInit (&argc, argv) ;
  glutInitDisplayMode (GLUT_DOUBLE | GLUT_RGB | GLUT_DEPTH) ;
  glutInitWindowSize (500, 500) ;
  glutInitWindowPosition (100, 100) ;
  glutCreateWindow(((char**)argv)[0]) ;
  initialize () ;
  glutReshapeFunc (reshape) ;
  glutKeyboardFunc (keyboard) ;
  glutDisplayFunc (display) ;
  glutMainLoop () ;
} /* end of [mainats] */

%}

(* ****** ****** *)

(* end of [glBlending2.dats] *)
