//expect:w213

function foo(x) {
  if (x == 1) {
    x /= 4
    ::print(x)
  }
  else {
    x /= 4
    ::print(x)
  }
}