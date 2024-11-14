import jatyc.lib.Typestate;
import jatyc.lib.Requires;
import jatyc.lib.Ensures;
import jatyc.lib.Nullable;

@Typestate("JavaIterator.protocol")
public final class JavaIterator {
  public boolean hasNext() {
    return false;
  }
  public String next() {
    return "";
  }
}
