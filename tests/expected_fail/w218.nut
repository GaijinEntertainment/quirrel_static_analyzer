//expect:w218

function foo(x) {
  do {
    if (::a == x)
      ::h(::a, x)
    continue;
    x--;
  } while (x)
}