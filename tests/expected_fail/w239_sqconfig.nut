//expect:w239

function returnBoolFunctionName() {
  if (::serverName == "")
    return

  return true;
}
