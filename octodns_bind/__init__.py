#
#
#

import socket
from datetime import datetime
from logging import getLogger
from os import listdir, makedirs
from os.path import exists, isdir, join
from string import Template

import dns.name
import dns.query
import dns.rdatatype
import dns.resolver
import dns.zone
from dns import tsigkeyring
from dns.exception import DNSException
from dns.update import Update as DnsUpdate

from octodns.provider.base import BaseProvider
from octodns.record import Create, Record, Rr, Update
from octodns.source.base import BaseSource

# TODO: remove once we require python >= 3.11
try:  # pragma: no cover
    from datetime import UTC
except ImportError:  # pragma: no cover
    from datetime import timedelta, timezone
    UTC = timezone(timedelta())

# TODO: remove __VERSION__ with the next major version release
__version__ = __VERSION__ = '0.0.6'


class RfcPopulate:
    SUPPORTS_DYNAMIC = False
    SUPPORTS_GEO = False
    SUPPORTS_MULTIVALUE_PTR = True
    SUPPORTS_ROOT_NS = True

    SUPPORTS = set(
        (
            'A',
            'AAAA',
            'CAA',
            'CNAME',
            'LOC',
            'MX',
            'NS',
            'PTR',
            'SPF',
            'SRV',
            'SSHFP',
            'TLSA',
            'TXT',
        )
    )

    def populate(self, zone, target=False, lenient=False):
        self.log.debug('populate: name=%s, target=%s, lenient=%s',
            zone.decoded_name, target, lenient)

        before = len(zone.records)
        rrs = self.zone_records(zone.name, target=target)
        for record in Record.from_rrs(zone, rrs, lenient=lenient):
            zone.add_record(record, lenient=lenient)

        self.log.info('populate:   found %s records', len(zone.records) - before)
        return self.zone_exists(zone.name, target)


class ZoneFileSourceException(Exception):
    pass


class ZoneFileSourceNotFound(ZoneFileSourceException):
    def __init__(self, path):
        super().__init__(f'Zone file not found at {path}')


class ZoneFileSourceLoadFailure(ZoneFileSourceException):
    def __init__(self, error):
        super().__init__(str(error))


class ZoneFileProvider(RfcPopulate, BaseProvider):
    '''
    Provider that reads and writes BIND style zone files

    config:
        class: octodns_bind.ZoneFileProvider

        # The location of zone files. Records are defined in a
        # file named for the zone in this directory, e.g.
        # something.com., including the trailing ., see `file_extension` below
        # (required)
        directory: ./config

        # The extension to use when working with zone files. It is appended onto
        # the zone name to determine the file when reading or writing
        # records. Some operating systems do not allow filenames ending with a .
        # and this value may need to be changed when working on them, e.g. to
        # .zone. The leading . should be included.
        # (default: .)
        file_extension: .

        # Wether the provider should check for the existence a root NS record
        # when loading a zone
        # (default: true)
        check_origin: true

        # The details of the SOA record can be customized when creating
        # zonefiles with the following options.
        default_ttl: 3600

        # Primary name server name or FQDN (ending with a dot) for zones
        # without a SOA record (new zones). If this name does not end with a
        # dot, the current zone name will be appended to this value.
        # (default: ns)
        primary_nameserver: ns

        # The email username or full address to be used when creating zonefiles.
        # If this is just a username, no @[domain.com.], the current zone name
        # will be appended to this value. If the value is a complete email
        # address it will be used as-is. Note that the actual email address with
        # a @ should be used and not the zone file format with the value
        # replaced with a `.`.
        # (default: webmaster)
        hostmaster_email: webmaster

        # The rest of the default SOA record
        serial: 0
        refresh: 3600
        retry: 600
        expire: 604800
        nxdomain: 3600
    '''

    def __init__(self, id, directory, file_extension='.',
        check_origin=True, default_ttl=3600,
        primary_nameserver='ns', hostmaster_email='webmaster', serial=0,
        refresh=10800, retry=3600, expire=604800, nxdomain=60,
        apply_disabled=False, strict_supports=True,
    ):
        self.log = getLogger(f'{self.__class__.__name__}[{id}]')
        self.log.debug(f'__init__: id={id}, directory={directory}, file_extension={file_extension}, check_origin={check_origin}, default_ttl={default_ttl}, '
            f'primary_nameserver={primary_nameserver} hostmaster_email={hostmaster_email}, refresh={refresh}, retry={retry}, expire={expire}, nxdomain={nxdomain}, '
            f'apply_disabled={apply_disabled}, strict_supports={strict_supports}')

        super().__init__(id, apply_disabled=apply_disabled, strict_supports=strict_supports)

        self.directory = directory
        self.file_extension = file_extension
        self.check_origin = check_origin
        self.hostmaster_email = hostmaster_email
        self.default_ttl = default_ttl
        self.refresh = refresh
        self.retry = retry
        self.expire = expire
        self.nxdomain = nxdomain

        self._zone_soa = {}
        self._zone_records = {}

    def list_zones(self):
        n = len(self.file_extension)
        for filename in sorted(listdir(self.directory)):
            if filename.endswith(self.file_extension):
                if n > 0:
                    filename = filename[:-n]
                yield f'{filename}.'

    def _load_zone_file(self, zone_name, target):
        if target:
            # if we're in target mode we assume nothing exists b/c we recreate
            # everything every time, similar to YamlProvider
            return None

        zone_filename = f'{zone_name[:-1]}{self.file_extension}'
        zonefiles = listdir(self.directory)
        path = join(self.directory, zone_filename)
        if zone_filename in zonefiles:
            try:
                z = dns.zone.from_file(
                    path,
                    zone_name,
                    relativize=False,
                    check_origin=self.check_origin,
                )
            except DNSException as error:
                raise ZoneFileSourceLoadFailure(error)
        else:
            raise ZoneFileSourceNotFound(path)

        return z

    def zone_path(self, zone_name):
         zone_filename =  f'{zone_name[:-1]}{self.file_extension}'
         return join(self.directory, zone_filename)

    def zone_exists(self, zone_name, target=False):
        return exists(self.zone_path(zone_name))

    def encode_email(self, email, zone_name=''):
        # escape any .'s in the email username
        pieces = email.split('@')
        pieces[0] = pieces[0].replace('.', '\\.')
        if len(pieces) == 2: return f'{pieces[0]}.{pieces[1]}'
        return f'{pieces[0]}.{zone_name}'

    def decode_email(self, encoded_email):
        email = encoded_email.replace(r'\.', '\n').replace('.', '@', 1).replace('\n', '.')
        self.log.debug(f'decode_email: {encoded_email!r} -> {email!r}')
        return email

    def zone_records(self, zone_name, target):
        self.log.debug(f'zone_records: {zone_name} target={target}')

        if records := self._zone_records.get(zone_name):
            return records

        records = []
        soa = {
            'zone_name': zone_name,
            'default_ttl': self.default_ttl,
            'primary_nameserver': '',
            'hostmaster_email': '',
            'serial': self._serial(),
            'refresh': self.refresh,
            'retry': self.retry,
            'expire': self.expire,
            'nxdomain': self.nxdomain,
        }

        if dns_zone := self._load_zone_file(zone_name, target):
            for name, ttl, rdata in dns_zone.iterate_rdatas():
                rdtype = dns.rdatatype.to_text(rdata.rdtype)

                if str(name) == zone_name and rdtype == 'SOA':
                    self.log.debug(f'zone_records: {name} {ttl} SOA mname={rdata.mname} rname={rdata.rname} serial={rdata.serial} refresh={rdata.refresh} retry={rdata.retry} expire={rdata.expire} minimum={rdata.minimum}')
                    soa.update({
                        'default_ttl': ttl,
                        'primary_nameserver': str(rdata.mname),
                        'hostmaster_email': self.decode_email(str(rdata.rname)),
                        'serial': rdata.serial,
                        'refresh': rdata.refresh,
                        'retry': rdata.retry,
                        'expire': rdata.expire,
                        'nxdomain': rdata.minimum
                    })
                    continue

                if rdtype not in self.SUPPORTS:
                    self.log.warning(f'zone_records: skipping {name} {ttl} {rdata!r}')
                    continue

                records.append(Rr(name.to_text(), rdtype, ttl, rdata.to_text()))

        self._zone_records[zone_name] = records
        self._zone_soa[zone_name] = soa
        return records

    def zone_soa(self, zone_name, target):
        rrs = self.zone_records(zone_name, target)
        return self._zone_soa[zone_name]

    def _primary_nameserver(self, decoded_name, records):
        for record in records:
            if record.name == '' and record._type == 'NS':
                return record.values[0]
        self.log.warning(
            '_primary_nameserver: unable to find a primary_nameserver for %s, using placeholder',
            decoded_name,
        )
        return f'ns.{decoded_name}'

    def _hostmaster_email(self, decoded_name):
        pieces = self.hostmaster_email.split('@')
        # escape any .'s in the email username
        pieces[0] = pieces[0].replace('.', '\\.')
        if len(pieces) == 2:
            return '.'.join(pieces)

        return f'{pieces[0]}.{decoded_name}'

    def _longest_name(self, records):
        try:
            return sorted(len(r.name) for r in records)[-1]
        except IndexError:
            return 0

    def _now(self):
        return datetime.now(UTC)

    def _serial(self):
        # things wrap/reset at max int
        return int(self._now().timestamp()) % 2147483647

    def _apply(self, plan):
        desired = plan.desired
        name = desired.decoded_name

        if not isdir(self.directory):
            makedirs(self.directory)

        records = sorted(c.record for c in plan.changes)
        longest_name = self._longest_name(records)

        filename = join(self.directory, f'{name[:-1]}{self.file_extension}')
        with open(filename, 'w') as fh:
            template = Template(
                '''$$ORIGIN $zone_name

@ $default_ttl IN SOA $primary_nameserver $hostmaster_email (
    $serial ; Serial
    $refresh ; Refresh
    $retry ; Retry
    $expire ; Expire
    $nxdomain ; NXDOMAIN ttl
)

'''
            )

            primary_nameserver = self._primary_nameserver(name, records)
            fh.write(
                template.substitute(
                    {
                        'hostmaster_email': self._hostmaster_email(name),
                        'serial': self._serial(),
                        'zone_name': name,
                        'default_ttl': self.default_ttl,
                        'primary_nameserver': primary_nameserver,
                        'refresh': self.refresh,
                        'retry': self.retry,
                        'expire': self.expire,
                        'nxdomain': self.nxdomain,
                    }
                )
            )

            prev_name = None
            for record in records:
                try:
                    values = record.values
                except AttributeError:
                    values = [record.value]
                for value in values:
                    value = value.rdata_text
                    if record._type in ('SPF', 'TXT'):
                        # TXT values need to be quoted
                        value = value.replace('"', '\\"')
                        value = f'"{value}"'
                    name = '@' if record.name == '' else record.name
                    if name == prev_name:
                        name = ''
                    else:
                        prev_name = name
                    fh.write(
                        f'{name:<{longest_name}} {record.ttl:8d} IN {record._type:<8} {value}\n'
                    )

        self.log.debug(
            '_apply: zone=%s, num_records=%d', name, len(plan.changes)
        )

        self.log.debug('_apply: zone=%s, num_records=%d', zone_name, len(records))
        return True


ZoneFileSource = ZoneFileProvider


class AxfrSourceException(Exception):
    pass


class AxfrSourceZoneTransferFailed(AxfrSourceException):
    def __init__(self, err):
        super().__init__(f'Unable to Perform Zone Transfer: {err}')


class AxfrPopulate(RfcPopulate):
    def __init__( self, id, host, port=53, ipv6=False, timeout=15, key_name=None, key_secret=None, key_algorithm=None, **kw):
        self.log = getLogger(f'{self.__class__.__name__}[{id}]')
        self.log.debug(f'__init__: id={id}, port={port}, ipv6={ipv6}, timeout={timeout}, '
            f'key_name={key_name} key_secret={key_secret}, key_algorithm={key_algorithm}')

        super().__init__(id, **kw)
        self.host = self._host(host, ipv6)
        self.port = int(port)
        self.ipv6 = ipv6
        self.timeout = float(timeout)
        self.key_name = key_name
        self.key_secret = key_secret
        self.key_algorithm = key_algorithm

    def _host(self, host, ipv6):
        h = host
        try:
            # Determine if IPv4/IPv6 address
            dns.inet.af_for_address(host)
        except ValueError:
            address_family = socket.AF_INET
            if ipv6:
                address_family = socket.AF_INET6

            try:
                h = socket.getaddrinfo(host, None, address_family)[0][4][0]
            except OSError as err:
                raise AxfrSourceZoneTransferFailed(err)

        return h

    def _auth_params(self):
        params = {}
        if self.key_name is not None:
            params['keyring'] = tsigkeyring.from_text(
                {self.key_name: self.key_secret}
            )
        if self.key_algorithm is not None:
            params['keyalgorithm'] = self.key_algorithm
        return params

    def zone_exists(self, zone_name, target=False):
        # We can't create them so they have to already exist
        return True

    def zone_records(self, zone_name, target):
        auth_params = self._auth_params()
        try:
            dns_zone = dns.zone.from_xfr(
                dns.query.xfr(
                    self.host,
                    zone_name,
                    port=self.port,
                    timeout=self.timeout,
                    lifetime=self.timeout,
                    relativize=False,
                    **auth_params,
                ),
                relativize=False,
            )
        except DNSException as err:
            raise AxfrSourceZoneTransferFailed(err) from None

        records = []

        for name, ttl, rdata in dns_zone.iterate_rdatas():
            rdtype = dns.rdatatype.to_text(rdata.rdtype)
            if rdtype in self.SUPPORTS:
                records.append(Rr(name.to_text(), rdtype, ttl, rdata.to_text()))

        return records


class AxfrSource(AxfrPopulate, BaseSource):
    pass


class Rfc2136ProviderException(Exception):
    pass


class Rfc2136ProviderUpdateFailed(Rfc2136ProviderException):
    def __init__(self, err):
        super().__init__(f'Unable to perform update: {err}')


class Rfc2136Provider(AxfrPopulate, BaseProvider):
    '''
    RFC-2136 7.6: States it's not possible to create zones, so we'll assume they
    exist and let things blow up during apply if there are problems It's a
    little ugly to inherit from two things that both ultimiately inherit from
    BaseSource, but it works. Some refactor
    '''

    SUPPORTS_ROOT_NS = True

    def _apply(self, plan):
        desired = plan.desired
        auth_params = self._auth_params()
        update = DnsUpdate(desired.name, **auth_params)

        for change in plan.changes:
            record = change.record

            name, ttl, _type, rdatas = record.rrs
            if isinstance(change, Create):
                update.add(name, ttl, _type, *rdatas)
            elif isinstance(change, Update):
                update.replace(name, ttl, _type, *rdatas)
            else:  # isinstance(change, Delete):
                update.delete(name, _type, *rdatas)

        r: dns.message.Message = dns.query.tcp(
            update, self.host, port=self.port, timeout=self.timeout
        )
        if r.rcode() != dns.rcode.NOERROR:
            raise Rfc2136ProviderUpdateFailed(dns.rcode.to_text(r.rcode()))

        self.log.debug('_apply: zone=%s, num_records=%d', name, len(plan.changes))

        return True


BindProvider = Rfc2136Provider
