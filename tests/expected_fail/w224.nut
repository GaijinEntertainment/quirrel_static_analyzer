//expect:w224

function foo(x){
  while (x) {
    x++;
    if (x > 5)
      break;
  } while (x < 6) ;
}