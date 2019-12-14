//expect:w220

function foo(a){
  foreach(x in a?.y()) {
    ::print(x)
  }
}