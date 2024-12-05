open Common

let () =
  parse_and_print "ec.jazz"  "_ec";
  parse_and_print "ec.jazz"  "_ec2";
  parse_and_print "ec.jazz"  "_ec3";
  assert false
