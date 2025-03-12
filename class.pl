use Time::HiRes;
use URI;
use URI::Query;
use URI::URL;
use JSON;
use IO::Socket::INET;
$| = 1;
my $label = 1;
my @data;
use Net::Whois::Raw;
$Net::Whois::Raw::CHECK_FAIL = 1;
$Net::Whois::Raw::TIMEOUT = 10;

use Storable qw(retrieve);
use List::Util qw(sum min max);
my @accepted_chars = split( //, 'abcdefghijklmnopqrstuvwxyz ' );
my %pos        = map { $accepted_chars[$_] => $_ } 0 .. $#accepted_chars;
my $model_file = 'gib_model.dat';
my $model_data = retrieve($model_file);
my %exceptions = (
Rhythm => 1,
Sphynx => 1
);

local *normalize = sub {
  my ($line) = @_;
  grep { exists( $pos{$_} ) } split( //, lc($line) );
};

local *ngram = sub {
  my ( $n, $l ) = @_;

  my @filtered = normalize($l);

  my @ngram;
  foreach my $start ( 0 .. @filtered - $n ) {
    push @ngram, [ @filtered[ $start .. $start + $n - 1 ] ];
  }

  return @ngram;
};

local *avg_transition_prob = sub {
  my ( $l, $log_prob_mat ) = @_;

  my $log_prob      = 0;
  my $transition_ct = 0;

  foreach my $pair ( ngram( 2, $l ) ) {
    my $a = $pair->[0];
    my $b = $pair->[1];
    $log_prob += $log_prob_mat->[ $pos{$a} ][ $pos{$b} ];
    $transition_ct += 1;
  }
  return exp( $log_prob / ( $transition_ct || 1 ) );
};

local *calculate_string = sub {
  my ($word) = @_;

  if ( exists $exceptions{$word} ) {
    $result{$word} += 1;
    next;
  }

  my $model_mat = $model_data->{mat};
  my $threshold = $model_data->{thresh};

  my $prob = avg_transition_prob( $word, $model_mat );

  if ( $prob > $threshold ) {
    $result{$word} += 1;
  }
  else {
    $result{$word} -= 1;
  }

  my $sum  = sum( values %result );
  my $diff = $sum - @words;

  if ( $diff == 0 ) {
    return 0;
  }
  else {
    my @gibberish = grep { $result{$_} < 0 } @words;
    return 1 if (@gibberish);
  }
};

my $policies = 'companies.txt';
open my $handle, $policies;
my %company_names;
while (my $line = <$handle>) {
  $line =~ s/\s+//g;
  next if ($line =~ /google/);
  $company_names{$line} = 1;
}

print "this many company names\n";
print(scalar keys %company_names);
print "\n";

my $dictionary = 'words.txt';
open my $handle, $dictionary;
my %dict;
while (my $line = <$handle>) {
  $line = lc($line);
  $line =~ s/\s+//g;
  $dict{$line} = 1;
}

# foreach (sort {lc $a cmp lc $b} keys %attr_hash) {
#   print "$_,";
# }
sub company_in_dir {
  my @directories = shift;
  foreach my $company (keys %company_names) {
    foreach(@directories) {
      if ($_ =~ /$company/i) {
        return 1;
      }
    }
  }
}

sub get_match_count {
  my $string = shift;
  my $match = shift;
  return (() = $string =~ /(\Q$match\E)/gi);
}

sub get_opt_count {
  my $string = shift;
  my $delim_chars = shift;
  return (() = $string =~ /([\Q$delim_chars\E])/gi);
}

sub get_token_count {
  my $directories = shift;
  my $n_tokens = 0;
  foreach(@{$directories}) {
    $n_tokens += () = $_ =~ /([a-z0-9]+)/ig;
  }
  return $n_tokens;
}

sub is_known_extension {
  my $file = shift;
  $file =~ /[a-z0-9-]+\.([\w\.\-]+)/i;
  return 1 if ($1 =~ /(?:htm|html|php|asp|aspx|jsp|shtml|xhtml|xml|js)/);
  return 0;
}

sub is_crap_tld {
  my $string = shift;
  return 1 if ($string =~ /\.(?:accountant|bid|click|club|cricket|date|download|faith|ga|gdn|host|loan|link|ninja|online|party|reviews?|rocks|science|stream|site|space|tech|top|trade|webcam|win|work|xyz|today)(?:\/|$)/i);
  return 0;
}

# sub get_url_data {
#   my $data = whois($domain);
#
#   return ($mx_record, $domain_update_age, $domain_age, $domain_expiry_age, $a_record, $a_record_geo);
# }

use Net::Whois::Raw;
use DateTime qw( );
use Net::DNS;
my $dns = new Net::DNS::Resolver;

$Net::Whois::Raw::CHECK_FAIL = 1;

sub get_time_delta {
  my $data_re = shift;
  my ($y, $m, $d) = $data_re =~ /([0-9]{4})\-([0-9]{2})\-([0-9]{2})/;
  my $date = DateTime->new(
  year      => $y,
  month     => $m,
  day       => $d,
  time_zone => 'local',
  );
  my $delta = DateTime->now->epoch - $date->epoch;
  my $days = int($delta / (24 * 60 * 60));
  return $days;
}

use Geo::IP;
my $geoip = Geo::IP->new(GEOIP_MEMORY_CACHE);

sub get_url_data {
  my $domain = shift;
  my $uri = URI::URL->new($domain);
  my $data;
  eval { $data = whois($uri->host); };
  if (length $data < 1 || $@) {
    return -3,-1,-1,-1,-1,-1;
  }
  my ($mx_record, $domain_update_age, $domain_age, $domain_expiry_age, $a_record, $a_record_geo) = -1;

  my $update_re = $1 if ($data =~ /\s+(?:Updated?\sDate:\s+)(\d.+)T/i);
  my $create_re = $1 if ($data =~ /\s+(?:Creat(?:ed|ion)?\sDate:\s+)(\d.+)T/i);
  my $expire_re = $1 if ($data =~ /\s+(?:Registrar|registry|registration)\s(?:expiration|expiry)\sDate:\s+(\d.+?)T/i);

  my $domain_update_age = -1;
  my $domain_age = -1;
  my $domain_expiry_age = -1;
  if ($update_re) {
    $domain_update_age = (get_time_delta($update_re) || -1);
  }
  if ($create_re) {
    $domain_age = (get_time_delta($create_re) || -1);
  }
  if ($expire_re) {
    $domain_expiry_age = (get_time_delta($expire_re) || -1);
    $domain_expiry_age *= -1;
  }

  my $mx_record = -1;
  if ($dns->query($domain, 'MX')) {
    $mx_record = 1;
  } else {
    $mx_record = 0;
  }

  my $a = $dns->query($domain, 'A');
  my $a_record = -1;
  if ($a) {
    $a_record = 1;
  } else {
    $a_record = 0;
  }

  my $a_record_geo = -1;
  if ($a) {
    foreach $rr ($a->answer) {
      my $ip = $rr->address;
      $a_record_geo = $geoip->country_code_by_addr($ip);
    }
  }
  return ($mx_record, $domain_update_age, $domain_age, $domain_expiry_age, $a_record, $a_record_geo);
}

local *process_url = sub {
  my $url = shift;

  my %attr_hash = (
  #url_based
  'url_crap_tld' => 0,
  'url_len' => 0,
  'url_n_dot' => 0,
  'url_frag' => 0,
  #domain based
  'domain_len' => 0,
  'domain_ip' => 0,
  'domain_port' => 0,
  'domain_hypen' => 0,
  #directory based
  'dir_len' => 0,
  'n_subdir' => 0,
  'dir_max_len' => 0,
  'dir_n_dot' => 0,
  'dir_n_delim' => 0,
  'dir_n_token' => 0,
  'company_dir' => 0,
  # #file based
  'file_len' => 0,
  'file_n_delim' => 0,
  'file_known_type' => 0,
  # query based
  'query_len' => 0,
  'n_var' => 0,
  'var_max_len' => 0,
  # query value based
  'v_email' => 0,
  'v_max_len' => 0,
  'v_hex' => 0,
  #domain query based
  'mx_record' => "",
  'domain_update_age' => "",
  'domain_age' => "",
  'domain_expiry_age' => "",
  'a_record' => "",
  'a_record_geo' => "",
  # #character/token based
  'n_dict_words' => 0,
  'n_gib_words' => 0,
  # 'n_finance_words' => 0,

  # 'n_security_words' => 0,
  # 'n_account_words' => 0,
  'max_len_token' => 0,
  );

  if ($url !~ /^(?:https?|ftp):\/\//i) {
    $url = "http:\/\/" . $url;
  }

  my $uri = URI::URL->new($url);
  #URL Based
  $attr_hash{'url_len'} = length $url;
  $attr_hash{'url_n_dot'} = get_match_count($url, '.');

  $attr_hash{'url_crap_tld'} = 1 if (is_crap_tld($url));

  #Domain Based
  if (!$uri->can('host')) { print "Failed to parse URL! $url"; sleep 2; return; }
  my $domain = $uri->host;

  ($mx_record, $domain_update_age, $domain_age, $domain_expiry_age, $a_record, $a_record_geo) = get_url_data($url);
  if ($mx_record != -3) {
    $attr_hash{'mx_record'} = $mx_record;
    $attr_hash{'domain_update_age'} = $domain_update_age;
    $attr_hash{'domain_age'} = $domain_age;
    $attr_hash{'domain_expiry_age'} = $domain_expiry_age;
    $attr_hash{'a_record'} = $a_record;
    $attr_hash{'a_record_geo'} = $a_record_geo;
  }
  $attr_hash{'domain_len'} = length $domain;
  $attr_hash{'domain_ip'} = 1 if ($domain =~ /(?:\d{1,3}\.){3}\d{1,3}/);
  $attr_hash{'domain_port'} = 1 if ($uri->port != $uri->default_port);

  $domain =~ /([a-z0-9-.]*)(?:\.\w{2,}$)/i;
  my $cleaned_domain = $1;

  $attr_hash{'domain_hypen'} = get_match_count($domain, '-');


  my $dummy_url = 'https://www.domain.com';
  if ($uri->fragment) {
    $attr_hash{'url_frag'} = 1;
    $dummy_url .= $uri->fragment;
    $uri = URI::URL->new($dummy_url);
  }
  #directory based
  unless (length $uri->epath == 0) {
    my @segments = $uri->path_segments;
    my @directories;
    my $file;
    foreach(@segments) {
      next if (length $_ == 0);
      if ($_ =~ /([a-z0-9-]+\.(?:htm|html|js|php))/i) {
        $file = $_;
      } else {
        push @directories, $_;
      }
    }
    $attr_hash{'n_subdir'} = @directories + 0;

    my $max_len = 0;
    my $total_len = 0;
    my $total_dots = 0;
    my $total_delim = 0;

    if (company_in_dir(@directories)) {
      $attr_hash{'company_dir'} = 1;
    }

    foreach(@directories) {
      my $length = length $_;
      $total_len += $length;
      $max_len = $length if ($length > $max_len);
      $total_dots += get_match_count($_, '.');
      $total_delim += get_opt_count($_, '.-_~!$&()*+,;=:@');
    }
    $attr_hash{'dir_len'} = $total_len;
    $attr_hash{'dir_max_len'} = $max_len;
    $attr_hash{'dir_n_dot'} = $total_dots;
    $attr_hash{'dir_n_delim'} = $total_delim;
    $attr_hash{'dir_n_token'} = get_token_count(\@directories);

    my $largest = 0;
    foreach(@directories) {
      while($_ =~ /([a-z0-9]+)/ig){
        my $token = lc($1);
        my $temp = length $token;
        if (calculate_string($token)) {
          $attr_hash{'n_gib_words'} += 1;
        }
        if ($dict{$token}) {
          $attr_hash{'n_dict_words'} += 1;
        }
        $largest = $temp if ($temp > $largest);
      }
    }

    $attr_hash{'max_len_token'} = $largest;
    if (length $file > 0) {
      $attr_hash{'file_len'} = length $file;
      $attr_hash{'file_n_delim'} = get_opt_count($file, '-_~!$&()*+,;=:@');
      $attr_hash{'file_known_type'} = is_known_extension($file);
    }

    my $query_string = $uri->equery;
    $attr_hash{'query_len'} = (length $query_string) || 0;
    unless (length $query_string == 0) {
      my $query_hash = URI::Query->new($query_string)->hash;
      $attr_hash{'n_var'} = scalar keys %{$query_hash};

      my $var_max_len;
      my $v_max_len;
      foreach my $key (keys %{$query_hash}) {
        my $k_len = length $key;
        $var_max_len = $k_len if ($k_len > $var_max_len);
        my $value = $query_hash->{$key};
        my $v_len = length $value;
        $v_max_len = $v_len if ($v_len > $v_max_len);
        $attr_hash{'v_email'} = 1 if ($value =~ /[a-z0-9-+]\@[a-z0-9]/i);
        $attr_hash{'v_hex'} = 1 if ($value =~ /[a-f0-9]{16,}/i);
      }
      $attr_hash{'v_max_len'} = $v_max_len;
      $attr_hash{'var_max_len'} = $var_max_len;
    }
  }

  my @matrix;
  foreach (sort {lc $a cmp lc $b} keys %attr_hash) {
    if (!defined($attr_hash{$_})) {
      push @matrix, 0;
    } else {
      push @matrix, $attr_hash{$_};
    }
  }

  my %present_data = (
  'matrix' => \@matrix,
  'res' => $label,
  );
  push @data, \%present_data;
};

my $i = 1;
my $start = Time::HiRes::time();
my $file = 'bad.log';
open my $fh, $file;
while (my $line = <$fh>) {
  process_url($line);
  print "Processed $i \n" if ($i % 10000 == 0);
  $i++;
}

print ("Elapsed Time:" . (Time::HiRes::time() - $start) . "s\n");
print "Total number of entries " . length $data + "\n";
print "\n";


my $start = Time::HiRes::time();
my $file = 'good.log';
open my $fh, $file;
$label = 0;
while (my $line = <$fh>) {
  process_url($line);
}
print ("Elapsed Time:" . (Time::HiRes::time() - $start) . "s\n");
print "Total number of entries " . length $data + "\n";
print "\n";