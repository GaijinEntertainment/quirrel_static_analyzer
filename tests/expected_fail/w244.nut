//expect:w244

class A {
  function ns() {
  }

  static function fn() {
    ::print(ns())
  }
}
