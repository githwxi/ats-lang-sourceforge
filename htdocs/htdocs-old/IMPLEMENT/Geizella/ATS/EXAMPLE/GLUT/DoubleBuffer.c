#include <stdlib.h>
#include <stdio.h>
#include <GL/glut.h>

static GLfloat spin = 0.0;

void init(void) {
  glClearColor (0.0, 0.0, 0.0, 0.0);
  glShadeModel(GL_FLAT);
  return;
}

void display(void) {
  glClear(GL_COLOR_BUFFER_BIT);
  glPushMatrix();
  glRotatef(spin, 0.0, 0.0, 1.0);
  glColor3f(1.0, 1.0, 1.0);
  glRectf(-25.0, -25.0, 25.0, 25.0);
  glPopMatrix();
  glutSwapBuffers();
}

void spinDisplay(void) {
  spin += 2.0;
  if (spin > 360.0) spin -= 360.0;
  glutPostRedisplay();
  return;
}

void reshape(int w, int h) {
  glViewport(0, 0, (GLsizei)w, (GLsizei)h);
  glMatrixMode(GL_PROJECTION);
  glLoadIdentity();
  glOrtho(-50.0, 50.0, -50.0, 50.0, -1.0, 1.0);
  glMatrixMode(GL_MODELVIEW);
  glLoadIdentity();
  return;
}

void mouse(int button, int state, int x, int y) {
  /*
  printf ("mouse: button = %i\n", button);
  printf ("mouse: state = %i\n", state);
  printf ("mouse: GLUT_DOWN = %i\n", GLUT_DOWN);
  printf ("mouse: GLUT_LEFT_BUTTON = %i\n", GLUT_LEFT_BUTTON);
  printf ("mouse: GLUT_MIDDLE_BUTTON = %i\n", GLUT_MIDDLE_BUTTON);
  */

  switch (button) {
    case GLUT_LEFT_BUTTON:
      if (state == GLUT_DOWN) glutIdleFunc(spinDisplay); break;
    case GLUT_MIDDLE_BUTTON:
      if (state == GLUT_DOWN) glutIdleFunc(NULL); break;
    default: break;
  }
  return;
}

int main (int argc, char** argv) {
  glutInit(&argc, argv);
  glutInitDisplayMode(GLUT_DOUBLE | GLUT_RGB);
  glutInitWindowSize(250, 250);
  glutInitWindowSize(100, 100);
  glutCreateWindow(argv[0]);
  init();
  glutDisplayFunc(display);
  glutReshapeFunc(reshape);
  glutMouseFunc(mouse);
  glutMainLoop();
  return 0;
}
