%{^

extern ats_void_type mainats (ats_int_type argc, ats_ptr_type argv) ;

%}

staload "libc/GL/SATS/gl.sats"
staload "libc/GL/SATS/glut.sats"

extern fun initialize (): void = "initialize"
implement initialize () = let
  val () = glClearColor (0.0, 0.0, 0.0, 0.0)
  val () = glMatrixMode (GL_PROJECTION)
  val () = glLoadIdentity ()
  val () = glOrtho (0.0, 1.0, 0.0, 1.0, ~1.0, 1.0)
in
  // empty
end // end of [initialize]


extern fun display (): void = "display"
implement display () = let
  val () = glClear (GL_COLOR_BUFFER_BIT)
  val () = glColor3f (1.0, 1.0, 1.0)
  val (pf | ()) = glBegin (GL_POLYGON)
  val () = glVertex3f (0.25, 0.25, 0.0)
  val () = glVertex3f (0.75, 0.25, 0.0)
  val () = glVertex3f (0.75, 0.75, 0.0)
  val () = glVertex3f (0.25, 0.75, 0.0)
  val () = glEnd (pf | (*none*))
  val () = glFlush ()
in
  // empty
end // end of [display]

//

implement main_dummy () = ()

%{$

ats_void_type mainats
  (ats_int_type argc, ats_ptr_type argv) {

  glutInit ((int*)&argc, (char**)argv) ;
  glutInitDisplayMode (GLUT_SINGLE | GLUT_RGB) ;
  glutInitWindowSize (500, 500) ;
  glutInitWindowPosition (100, 100) ;
  glutCreateWindow("Hello!") ;
  initialize () ;
  glutDisplayFunc (display) ;
  glutMainLoop () ;
  return ; /* deadcode */
}

%}

(* ****** ****** *)

(* end of [glHello.dats] *)
