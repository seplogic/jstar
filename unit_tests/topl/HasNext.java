// Use an iterator without checking that it is ok.

import java.util.*;

class HasNext {
  public static void main(String[] args) {
    Collection<Integer> c = make(1, 2);
    print(c.iterator());
  }

  static Collection<Integer> make(int x, int y) {
    Collection<Integer> r = new ArrayList<Integer>();
    r.add(x);
    r.add(y);
    return r;
  }

  static void print(Iterator<Integer> i) {
    if (i.hasNext()) i.next();
  }

  static void printBad(Iterator<Integer> i) {
    do System.out.println(i.next());    // BUG
    while (i.hasNext());
  }
}
