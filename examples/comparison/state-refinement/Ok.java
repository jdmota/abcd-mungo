import jatyc.lib.Requires;
import jatyc.lib.Ensures;
import jatyc.lib.State;

public class Ok {

  public static void main() {
    File f = createFile();

    switch (f.open()) {
      case OK:
        read(f);
        f.close();
        break;
      case ERROR:
        break;
    }
  }

  public static @State("Init") File createFile() {
    return new File();
  }

  public static void read(@Requires("Read") @Ensures("Close") final File f) {
    f.read();
  }

}
