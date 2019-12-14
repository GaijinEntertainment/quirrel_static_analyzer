//expect:w217

function foo(x){
  while (x) {
    if (::a == x)
      ::h(::a, x)

    return
  }
}