#sudo apt-get install libdbd-sqlite3-perl libdbi-perl
use strict;
use warnings;
use Getopt::Long;
use DBI;

# Connect to database
my $dbfile = $ENV{'HOME'} . "/.keymaerax/keymaerax.sqlite";
die 'Could not find ' . $dbfile unless -e $dbfile;
my $dbh = DBI->connect("dbi:SQLite:dbname=$dbfile", "", "") or die 'Could not connect to ' . $dbfile;


# Get params and validate input.
my $host;
my $port;
GetOptions(
  '--host=s' => \$host,
  '--port=i' => \$port
);
$port = 8080 unless $port;


# Update database.
$dbh->do("delete from config where configName='serverconfig'");
if($host) {
  $dbh->do("insert into config (configName, key, value) VALUES('serverconfig', 'host', '$host') ");
  $dbh->do("insert into config (configName, key, value) VALUES('serverconfig', 'port', '$port')");
  $dbh->do("insert into config (configName, key, value) VALUES('serverconfig', 'isHosted', 'true')");
  print "KeYmaera X will bind to $host:$port.\n"
}
else {
  print "No --host defined, so KeYmaera X will now bind to localhost:8090.\n";
}
exit 0;
__END__
=head1 Author

Nathan Fulton
nathanfu@cs.cmu.edu
=cut
