import jatyc.lib.*;

public class TSSubtyping {
  public static void main1() {
    B b = new B(); // [B1]
    // :: warning: (b: State{B, B1})
    b.m1(); // [B2]

    A a = null;

    if (someBool()) {
      // :: warning: (a: Null)
      // :: warning: (b: State{B, B2})
      a = b; // [A2, B2]
    } else {
      // :: warning: (b: State{B, B2})
      b = (B) change(b); // [A2] -> [B2 | B3]
      // :: warning: (a: Null)
      // :: warning: (b: State{B, B2} | State{B, B3})
      a = b; // [A2, B2 | B3]
    }

    // :: warning: (b: Shared{B})
    // :: warning: (a: (State{A, A2} & State{A, end}))
    b = (B) a; // [B2 | B3]

    // :: error: (Cannot call [m3] on State{B, B2} | State{B, B3})
    // :: warning: (b: State{B, B2} | State{B, B3})
    b.m3();
  }

  public static void main2() {
    B b = new B(); // [B1]
    // :: warning: (b: State{B, B1})
    b.m1(); // [B2]

    A a = null;

    if (someBool()) {
      // :: warning: (b: State{B, B2})
      b = (B) change(b); // [A2] -> [B2 | B3]
      // :: warning: (a: Null)
      // :: warning: (b: State{B, B2} | State{B, B3})
      a = b; // [A2, B2 | B3]
    } else {
      // :: warning: (a: Null)
      // :: warning: (b: State{B, B2})
      a = b; // [A2, B2]
    }

    // :: warning: (b: Shared{B})
    // :: warning: (a: (State{A, A2} & State{A, end}))
    b = (B) a; // [B2 | B3]

    // :: error: (Cannot call [m3] on State{B, B2} | State{B, B3})
    // :: warning: (b: State{B, B2} | State{B, B3})
    b.m3();
  }

  private static boolean someBool() {
    return true;
  }

  private static @Ensures("A2") A change(@Requires("B2") B obj) {
    // :: warning: (obj: State{B, B2})
    obj.m3(); // B3
    // :: warning: (obj: State{B, B3})
    return obj;
  }
}
