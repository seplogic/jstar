class NodeLL
{
  int val;
  NodeLL next;
}

class LinkedList
{
  private NodeLL head;
  private NodeLL tail;

  public void sum_head_all()
  {
    NodeLL x = head;
    while (x != null)
    {
      x = x.next;
    }
  }
}
