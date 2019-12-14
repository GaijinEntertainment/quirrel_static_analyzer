//expect:w244

local class A {
  function ns() {
  }

  static function fn() {
    ::print(ns())
  }
}
