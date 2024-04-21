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
from octodns.idna import IdnaDict, idna_decode, idna_encode


# TODO: remove once we require python >= 3.11
try:  # pragma: no cover
    from datetime import UTC
except ImportError:  # pragma: no cover
    from datetime import timedelta, timezone
    UTC = timezone(timedelta())

# TODO: remove __VERSION__ with the next major version release
__version__ = __VERSION__ = '0.0.7'


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
            'DNAME',
            'WR',
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
        apply_disabled=False, strict_supports=True, supports_root_ns=True, supports_alias=False,
    ):
        self.log = getLogger(f'{self.__class__.__name__}[{id}]')
        self.log.debug(f'__init__: id={id}, directory={directory}, file_extension={file_extension}, check_origin={check_origin}, default_ttl={default_ttl}, '
            f'primary_nameserver={primary_nameserver} hostmaster_email={hostmaster_email}, refresh={refresh}, retry={retry}, expire={expire}, nxdomain={nxdomain}, '
            f'apply_disabled={apply_disabled}, strict_supports={strict_supports} supports_root_ns={supports_root_ns} supports_alias={supports_alias}')

        super().__init__(id, apply_disabled=apply_disabled, strict_supports=strict_supports)

        self.SUPPORTS_ROOT_NS = supports_root_ns
        if supports_alias: self.SUPPORTS = self.SUPPORTS | {'ALIAS'}
        self.directory = directory
        self.file_extension = file_extension
        self.check_origin = check_origin
        self.default_ttl = default_ttl

        self.primary_nameserver = primary_nameserver
        self.hostmaster_email = hostmaster_email
        self.serial = serial
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
                if n: filename = filename[:-n]
                yield idna_decode(filename) + '.'

    def load_zone_file(self, zone_name, target):
        self.log.debug(f'load_zone_file: {zone_name} target={target}')

        if self.zone_exists(zone_name):
            try:
                return dns.zone.from_file(
                    self.zone_path(zone_name),
                    zone_name,
                    relativize=False,
                    check_origin=self.check_origin,
                )
            except DNSException as error:
                raise ZoneFileSourceLoadFailure(error)

        # If zone doesn't exist and we're in target mode, return nothing
        if target:
            return None

        # Else something bad happened.
        raise ZoneFileSourceNotFound(self.zone_path(zone_name))

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
            'serial': self.serial,
            'refresh': self.refresh,
            'retry': self.retry,
            'expire': self.expire,
            'nxdomain': self.nxdomain,
        }

        if dns_zone := self.load_zone_file(zone_name, target):
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

    def update_primary_nameserver(self, soa):
        zone_name = soa['zone_name']
        if primary_nameserver := soa['primary_nameserver']:
            return

        for record in self._zone_records[zone_name]:
            if record.name == '' and record._type == 'NS':
                self.log.debug(f'update_primary_nameserver: {record.name} {record._type} {record.values[0]}')
                primary_nameserver = record.values[0]

        if not primary_nameserver:
            self.log.debug(f'update_primary_nameserver: unable to find a primary for {zone_name}, using {self.primary_nameserver!r}')
            if self.primary_nameserver[-1:] == '.': primary_nameserver = self.primary_nameserver
            else: primary_nameserver = f'{self.primary_nameserver}.{zone_name}'

        self.log.debug(f'update_primary_nameserver: changed to {primary_nameserver!r}')
        soa['primary_nameserver'] = primary_nameserver

    def update_hostmaster_email(self, soa):
        zone_name = soa['zone_name']
        if hostmaster_email := soa['hostmaster_email']:
            return

        pieces = self.hostmaster_email.split('@')
        if len(pieces) == 2: hostmaster_email = f'{pieces[0]}@{pieces[1]}'
        else: hostmaster_email = f'{pieces[0]}@{zone_name}'

        self.log.debug(f'update_hostmaster_email: changed to {hostmaster_email!r}')
        soa['hostmaster_email'] = hostmaster_email

    def update_serial(self, soa):
        zone_name = soa['zone_name']
        serial = old_serial = soa['serial']

        new_serial = int(datetime.now(UTC).strftime('%Y%m%d00'))
        if new_serial > serial: serial = new_serial
        serial += 1

        self.log.debug(f'update_serial: {old_serial} -> {serial}, {zone_name}')
        soa['serial'] = serial

    def _apply(self, plan):
        self.log.debug('_apply: plan=%s, nchanges=%d', plan, len(plan.changes))

        if not isdir(self.directory):
            makedirs(self.directory)

        desired = plan.desired
        zone_name = desired.name

        soa = self.zone_soa(zone_name, target=True)
        self.update_primary_nameserver(soa)
        self.update_hostmaster_email(soa)
        self.update_serial(soa)

        with open(self.zone_path(zone_name), 'w') as fh:
            template = '''
$ORIGIN	{zone_name}	; {decoded_name}
$TTL	{default_ttl}
@	{default_ttl}	SOA	{primary_nameserver} {hostmaster_email_enc} (
\t\t	{serial} {refresh} {retry} {expire} {nxdomain} )\t; serial refresh retry expire negttl
            '''.strip() + '\n\n'

            fh.write(template.format(** soa | {
                'hostmaster_email_enc': self.encode_email(soa['hostmaster_email'], soa['zone_name']),
                'decoded_name': desired.decoded_name,
            }))

            prev_name = None
            records = sorted(desired.records)
            for record in records:
                if record.ignored:
                    self.log.debug('_apply:  skipping record=%s %s - %s ignored', record.fqdn, record._type, self.id)
                    continue
                elif len(record.included) > 0 and self.id not in record.included:
                    self.log.debug('_apply:  skipping record=%s %s - %s not included', record.fqdn, record._type, self.id)
                    continue
                elif self.id in record.excluded:
                    self.log.debug('_apply:  skipping record=%s %s - %s excluded', record.fqdn, record._type, self.id)
                    continue

                try:
                    values = record.rr_values
                except AttributeError:
                    values = [record.value]

                self.log.debug(f'_apply: record {record.name} {record._type} {values} {record.included}')
                for value in values:
                    name = record.name
                    if name == prev_name: name = ''
                    else: prev_name = name
                    comment = '\t; %s' % record.octodns['comment'] if 'comment' in record.octodns else ''
                    fh.write(f'{name:<23} {record.ttl:<6d} {record._type:<8} {value.rdata_text}{comment}\n')

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
