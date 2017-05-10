#!/usr/bin/perl

sub rand_pref {
  return 1 + int (rand (4));
}

$n = $ARGV[0];
for ($i = 0; $i < $n; $i++) {
  print "(A, "; print rand_pref; print "); ";
  print "(B, "; print rand_pref; print "); ";
  print "(C, "; print rand_pref; print "); ";
  print "(D, "; print rand_pref; print ")\n";
}
