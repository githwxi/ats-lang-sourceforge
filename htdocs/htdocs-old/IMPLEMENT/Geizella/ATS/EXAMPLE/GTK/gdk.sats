abst@ype GdkEventType = $extern "GdkEventType"

macdef GDK_BUTTON_PRESS = $extval (GdkEventType, "GDK_BUTTON_PRESS")

fun gevent_is_butten_press
  (gevent @ l | ptr l) -> (either (gevent @ l, gevent_button @ l, i) | int i)
