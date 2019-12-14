//expect:w220

function foo(a){
  local container = a?.y()
  foreach(x in container) {
    ::print(x)
  }
}