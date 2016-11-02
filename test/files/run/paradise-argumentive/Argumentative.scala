object Test extends App {
  @argumentative(1, 2) object X
  assert(X.toString == "1 2")
}
