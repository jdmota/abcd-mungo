import jatyc.lib.Typestate;

@Typestate("WeldingRobotProtocol")
public class WeldingRobot extends Robot {
  public WeldingRobot() {
  }

  public void turnOn() {
    // overriding
  }

  public boolean weldMetal() {
    return true;
  }

  public void heating() {
  }
}
