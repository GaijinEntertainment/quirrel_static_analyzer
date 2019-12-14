//expect:w227

function foo(a) {
  local b = function() {
    local x = 1
    local a = x
    ::print(a)
    return x
  }
  return b()
}