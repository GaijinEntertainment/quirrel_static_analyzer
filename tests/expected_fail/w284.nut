//expect:w284

function fn(x) {
  return ::y(x)
}

return fn(1) != null ? fn(1) : null
