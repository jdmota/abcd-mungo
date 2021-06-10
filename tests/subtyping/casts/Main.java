import org.checkerframework.checker.jtc.lib.Requires;
import org.checkerframework.checker.jtc.lib.State;

public class Main {

  public static void upcastBase(Base base) {

  }

  public static void upcastObject(Object obj) {

  }

  public static void main1() {
    Derived d = new Derived();
    // :: warning: (d: State{Derived, HasNext})
    Base b = d;
    // :: warning: (b: State{Derived, HasNext} | State{Derived, Remove})
    while (b.hasNext()) {
      // :: warning: (b: State{Derived, Next} | State{Derived, NextRemove})
      b.next();
    }
  }

  // :: error: ([d] did not complete its protocol (found: State{Derived, Remove} | State{Derived, end}))
  public static void main2() {
    Derived d = new Derived();
    // :: warning: (d: State{Derived, HasNext})
    if (d.hasNext()) {
      // :: warning: (d: State{Derived, Next})
      d.next();
    }
    // :: warning: (d: State{Derived, Remove} | State{Derived, end})
    upcastBase(d);
  }

  public static void main3() {
    Derived d = new Derived();
    // :: warning: (d: State{Derived, HasNext} | State{Derived, Remove})
    while (d.hasNext()) {
      // :: warning: (d: State{Derived, Next} | State{Derived, NextRemove})
      d.next();
    }
    // :: warning: (d: State{Derived, end})
    upcastBase(d);
  }

  public static void main4() {
    Base b = new Derived();
    // :: warning: (b: State{Derived, HasNext} | State{Derived, Remove})
    while (b.hasNext()) {
      // :: warning: (b: State{Derived, Next} | State{Derived, NextRemove})
      b.next();
    }
  }

  public static void main5() {
    Derived d = new Derived();
    // :: warning: (d: State{Derived, HasNext})
    helper(d);
  }

  public static void main6() {
    Derived d = new Derived();
    // :: warning: (d: State{Derived, HasNext})
    if (d.hasNext()) {
      // :: warning: (d: State{Derived, Next})
      d.next();
    }
    // :: warning: (d: State{Derived, Remove} | State{Derived, end})
    // :: error: (Incompatible parameter because State{Derived, Remove} | State{Derived, end} is not a subtype of State{Base, HasNext})
    helper(d);
  }

  public static void helper(@Requires("HasNext") Base b) {
    // :: warning: (b: State{Base, HasNext})
    while (b.hasNext()) {
      // :: warning: (b: State{Base, Next})
      b.next();
    }
  }

  public static @State("HasNext") Base helper2() {
    return new Derived();
  }

  public static @State("HasNext") Base helper3() {
    Derived d = new Derived();
    // :: warning: (d: State{Derived, HasNext})
    if (d.hasNext()) {
      // :: warning: (d: State{Derived, Next})
      d.next();
    }
    // :: warning: (d: State{Derived, Remove} | State{Derived, end})
    // :: error: (Incompatible return value because State{Derived, Remove} | State{Derived, end} is not a subtype of State{Base, HasNext})
    return d;
  }

  public static void main7() {
    Base b = (Base) new Derived();
    // :: warning: (b: State{Derived, HasNext} | State{Derived, Remove})
    while (b.hasNext()) {
      // :: warning: (b: State{Derived, Next} | State{Derived, NextRemove})
      b.next();
    }
  }

  // :: error: ([d] did not complete its protocol (found: State{Derived, Remove} | State{Derived, end}))
  public static void main8() {
    Derived d = new Derived();
    // :: warning: (d: State{Derived, HasNext})
    if (d.hasNext()) {
      // :: warning: (d: State{Derived, Next})
      d.next();
    }
    // :: warning: (d: State{Derived, Remove} | State{Derived, end})
    upcastBase(d);
  }

  public static void main9() {
    Derived d = new Derived();
    // :: warning: (d: State{Derived, HasNext})
    Base b = (Base) d;
    // :: warning: (b: State{Derived, HasNext})
    Derived d2 = (Derived) b;
    // :: warning: (d2: State{Derived, HasNext} | State{Derived, Remove})
    while (d2.hasNext()) {
      // :: warning: (d2: State{Derived, Next} | State{Derived, NextRemove})
      d2.next();
    }
  }

  public static void main10() {
    Derived d = new Derived();
    // :: warning: (d: State{Derived, HasNext})
    Base b = (Base) d;
    // :: warning: (b: State{Derived, HasNext} | State{Derived, Remove})
    while (b.hasNext()) {
      // :: warning: (b: State{Derived, Next} | State{Derived, NextRemove})
      b.next();
    }
    // :: warning: (b: State{Derived, end})
    Derived d2 = (Derived) b;
  }

  // :: error: ([d2] did not complete its protocol (found: State{Derived, Remove} | State{Derived, end}))
  public static void main11() {
    Derived d = new Derived();
    // :: warning: (d: State{Derived, HasNext})
    Base b = (Base) d;
    // :: warning: (b: State{Derived, HasNext})
    if (b.hasNext()) {
      // :: warning: (b: State{Derived, Next})
      b.next();
    }
    // :: warning: (b: State{Derived, Remove} | State{Derived, end})
    Derived d2 = (Derived) b;
  }

  // :: error: ([d2] did not complete its protocol (found: State{Derived, Next} | State{Derived, end}))
  public static void main12() {
    Derived d = new Derived();
    // :: warning: (d: State{Derived, HasNext})
    Base b = (Base) d;
    // :: warning: (b: State{Derived, HasNext})
    b.hasNext();
    // :: warning: (b: State{Derived, Next} | State{Derived, end})
    Derived d2 = (Derived) b;
  }

  // :: error: ([alias] did not complete its protocol (found: State{Derived, HasNext}))
  public static void main13() {
    Derived d = new Derived();
    // :: warning: (d: State{Derived, HasNext})
    Object alias = d;
  }

  // :: error: ([d] did not complete its protocol (found: State{Derived, HasNext}))
  public static void main14() {
    Derived d = new Derived();
    // :: warning: (d: State{Derived, HasNext})
    upcastObject((Object) d);
  }

  public static void main15(@Requires("HasNext") Base b) {
    // :: warning: (b: State{Base, HasNext})
    if (b instanceof Derived) {
      // :: warning: (b: (State{Derived, ?} & State{Base, HasNext}))
      while (b.hasNext()) {
        // :: warning: (b: (State{Derived, ?} & State{Base, Next}))
        b.next();
      }
    } else {
      // :: warning: (b: State{Base, HasNext})
      while (b.hasNext()) {
        // :: warning: (b: State{Base, Next})
        b.next();
      }
    }
  }

}
