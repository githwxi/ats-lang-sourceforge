%{^

extern ats_void_type mainats (ats_int_type argc, ats_ptr_type argv) ;

%}

staload "libc/GL/SATS/gl.sats"
staload "libc/GL/SATS/glut.sats"

(* ****** ****** *)

extern fun initialize (): void = "initialize"
implement initialize () = let
  val () = glClearColor (0.0, 0.0, 0.0, 0.0)
  val () = glShadeModel (GL_SMOOTH)
in
  // empty
end // end of [initialize]

fn drawTriangle (): void = let
  val (pf | ()) = glBegin (GL_TRIANGLES)
  val () = glColor3f (1.0, 0.0, 0.0)
  val () = glVertex2f (5.0, 5.0)
  val () = glColor3f (0.0, 1.0, 0.0)
  val () = glVertex2f (25.0, 5.0)
  val () = glColor3f (0.0, 0.0, 1.0)
  val () = glVertex2f (5.0, 25.0)
  val () = glEnd (pf | (*none*))
in
  // empty
end

extern fun display (): void = "display"
implement display () = let
  val () = glClear (GL_COLOR_BUFFER_BIT)
  val () = drawTriangle ()
  val () = glFlush ()
in
  // empty
end

local

typedef GLdouble = double

in

extern fun gluOrtho2D
  (_: double, _: double, _: double, _: double): void = "gluOrtho2D"

end

extern fun reshape (w: int, h: int): void = "reshape"
implement reshape (w, h) = let
  val () = glViewport (
    GLint_of_int 0, GLint_of_int 0, GLsizei_of_int w, GLsizei_of_int h
  )
  val () = glMatrixMode (GL_PROJECTION)
  val () = glLoadIdentity ()
  val () = case+ 0 of
    | _ when h <= w => gluOrtho2D
        (0.0, 30.0, 0.0, 30.0 * (double_of w) / (double_of h))
    | _ (* w < h *) => gluOrtho2D
        (0.0, 30.0 * (double_of w) / (double_of h), 0.0, 30.0)
  val () = glMatrixMode (GL_MODELVIEW)
in
  // empty
end // end of [reshape]

(* ****** ****** *)

implement main_dummy () = ()

(* ****** ****** *)

%{$

ats_void_type mainats
  (ats_int_type argc, ats_ptr_type argv) {

  glutInit ((int*)&argc, (char**)argv) ;
  glutInitDisplayMode (GLUT_SINGLE | GLUT_RGB | GLUT_DEPTH) ;
  glutInitWindowSize (500, 500) ;
  glutInitWindowPosition (100, 100) ;
  glutCreateWindow(((char**)argv)[0]) ;
  initialize () ;
  glutDisplayFunc (display) ;
  glutReshapeFunc (reshape) ;
  glutMainLoop () ;
  return ; /* deadcode */
}

%}

(* ****** ****** *)

(* end of [glColoredTriangle.dats] *)
