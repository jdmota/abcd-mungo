import org.checkerframework.checker.mungo.lib.MungoTypestate;

@MungoTypestate("Cell.protocol")
public class Cell {

  private Item item;

  public Cell() {
    this.item = null;
  }

  public void setItem(Item item) {
    this.item = item;
  }

  public Item getItem() {
    return item;
  }
}
