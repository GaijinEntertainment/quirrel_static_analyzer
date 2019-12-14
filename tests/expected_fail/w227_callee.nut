//expect:w227

function recursive(x) {
  local recursive = ::callee()
  return recursive(x)
}

if (recursive)
  ::print(recursive)
