//expect:w283

function fn(x) {
  return ::y.cc ?? x ?? null
}
