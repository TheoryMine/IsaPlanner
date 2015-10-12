#!/usr/bin/perl
use strict;

my $fileloc = "browser_info/HOL/HOL_IsaP/critics/document.ps";

if (-f $fileloc) {
  system("gv $fileloc");
} else {
  print "\nNo Such file: $fileloc\n\n";
}
