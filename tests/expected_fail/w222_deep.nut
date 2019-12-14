//expect:w222

function foo(a,x,y) {
  local index = x < y
  ::print(a[index])
}