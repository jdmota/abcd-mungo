public class CondInfo {
  public static void test1() {
    JavaIterator it = new JavaIterator();
    while (true) {
      // :: warning: (it: State{JavaIterator, HasNext})
      boolean b = it.hasNext();
      if (b) {
        // :: warning: (it: State{JavaIterator, Next})
        it.next();
      } else {
        break;
      }
    }
  }

  // :: error: ([it] did not complete its protocol (found: State{JavaIterator, Next}))
  public static void test2() {
    JavaIterator it = new JavaIterator();
    while (true) {
      // :: warning: (it: State{JavaIterator, HasNext})
      boolean b = it.hasNext();
      if (!b) {
        // :: error: (Cannot call [next] on State{JavaIterator, end})
        // :: warning: (it: State{JavaIterator, end})
        it.next();
      } else {
        break;
      }
    }
  }

  // :: error: ([it] did not complete its protocol (found: State{JavaIterator, Next} | State{JavaIterator, end}))
  public static void test3() {
    JavaIterator it = new JavaIterator();
    while (true) {
      // :: warning: (it: State{JavaIterator, HasNext})
      boolean b = it.hasNext();
      b = true;
      if (b) {
        // :: error: (Cannot call [next] on State{JavaIterator, Next} | State{JavaIterator, end})
        // :: warning: (it: State{JavaIterator, Next} | State{JavaIterator, end})
        it.next();
      } else {
        break;
      }
    }
  }

  public static void test4() {
    JavaIterator it = new JavaIterator();
    while (true) {
      boolean b;
      // :: warning: (b: Null)
      // :: warning: (it: State{JavaIterator, HasNext})
      if (b = it.hasNext()) {
        // :: warning: (it: State{JavaIterator, Next})
        it.next();
      } else {
        break;
      }
    }
  }

  // :: error: ([it] did not complete its protocol (found: State{JavaIterator, Next}))
  public static void test5() {
    JavaIterator it = new JavaIterator();
    while (true) {
      boolean b;
      // :: warning: (b: Null)
      // :: warning: (it: State{JavaIterator, HasNext})
      if (!(b = it.hasNext())) {
        // :: error: (Cannot call [next] on State{JavaIterator, end})
        // :: warning: (it: State{JavaIterator, end})
        it.next();
      } else {
        break;
      }
    }
  }
}
