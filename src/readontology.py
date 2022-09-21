#!/usr/bin/python
# coding: utf-8

"""Definition of the `Ontology` class.
"""
from __future__ import unicode_literals
from __future__ import absolute_import

import io
import json
import os
import warnings
import operator
import six
import gzip
import datetime
import contextlib
import collections
import functools
import abc
import re
import string
import itertools

from six.moves.urllib.error import URLError, HTTPError
try:
	import lxml.etree as etree
except ImportError:
	import xml.etree.ElementTree as etree
from six.moves import map

__version__ = 'dev'
__author__ = 'Martin Larralde'
__author_email__ = 'martin.larralde@ens-paris-saclay.fr'
__license__ = "MIT"

try:                        # Use enums if possible to improve
	from enum import Enum   # output but don't have to dl enum32
except ImportError:         # backport as it's not that important
	Enum = object           # enough to truly depend on it


class OboSection(Enum):  # noqa: D101
	meta    = 1
	typedef = 2
	term    = 3

class OwlSection(Enum):  # noqa: D101
	ontology = 1
	classes  = 2
	axiom    = 3


owl_ns = {
    'dc':       "http://purl.org/dc/elements/1.1/",
    'doap':     "http://usefulinc.com/ns/doap#",
    'foaf':     "http://xmlns.com/foaf/0.1/",
    'meta':     "http://www.co-ode.org/ontologies/meta.owl#",
    'obo':      "http://purl.obolibrary.org/obo/",
    'oboInOwl': "http://www.geneontology.org/formats/oboInOwl#",
    'owl':      "http://www.w3.org/2002/07/owl#",
    'protege':  "http://protege.stanford.edu/plugins/owl/protege#",
    'rdf':      "http://www.w3.org/1999/02/22-rdf-syntax-ns#",
    'rdfs':     "http://www.w3.org/2000/01/rdf-schema#",
    'skos':     "http://www.w3.org/2004/02/skos/core#",
    'ubprop':   "http://purl.obolibrary.org/obo/ubprop#",
    'uberon':   "http://purl.obolibrary.org/obo/uberon#",
    'xsd':      "http://www.w3.org/2001/XMLSchema#",
}

owl_to_obo = {
    'hasDbXref': 'xref',
    'equivalentClass': 'equivalent_to',
    'inSubset': 'subset',
    'hasOBONamespace': 'namespace',
    'hasOBOFormatVersion': 'format-version',
    'imports': 'import',
}

obo_to_owl = {
	v:k for k,v in six.iteritems(owl_to_obo)
}

owl_synonyms = {
    "hasExactSynonym": "EXACT",
    "hasNarrowSynonym": "NARROW",
    "hasBroadSynonym": "BROAD",
    "hasRelatedSynonym": "RELATED",
    "hasSynonym": "RELATED"
}

@six.add_metaclass(abc.ABCMeta)
class BaseParser(object):
	"""An abstract parser object.
    """

	@classmethod
	@abc.abstractmethod
	def hook(cls, force=False, path=None, lookup=None):
		"""Test whether this parser should be used.

        The current behaviour relies on filenames, file extension
        and looking ahead a small buffer in the file object.
        """

	@classmethod
	@abc.abstractmethod
	def parse(self, stream):
		"""
        Parse the ontology file.

        Parameters
            stream (io.StringIO): A stream of ontologic data.

        Returns:
            (dict, dict, list): a tuple of metadata, dict, and imports.

        """

class ProntoWarning(Warning):
	"""A warning raised by pronto.

    Example:
        >>> from pronto import Ontology
        >>> import warnings
        >>> with warnings.catch_warnings(record=True) as w:
        ...    # the following ontology always has import issues (no URI in imports)
        ...    ims = Ontology('https://raw.githubusercontent.com/beny/imzml'
        ...                   '/master/data/imagingMS.obo')
        >>> print(w[-1].category)
        <class 'pronto.utils.ProntoWarning'>

    """

def unique_everseen(iterable):
	"""List unique elements, preserving order. Remember all elements ever seen."""
	# unique_everseen('AAAABBBCCDAABBB')    --> A B C D
	seen = set()
	seen_add = seen.add

	for element in six.moves.filterfalse(seen.__contains__, iterable):
		seen_add(element)
		yield element

def output_str(f):
	"""Create a function that always return instances of `str`.

    This decorator is useful when the returned string is to be used
    with libraries that do not support ̀`unicode` in Python 2, but work
    fine with Python 3 `str` objects.
    """
	if six.PY2:
		def new_f(*args, **kwargs):
		    return f(*args, **kwargs).encode("utf-8")
	else:
		new_f = f
	return new_f

def nowarnings(func):
	"""Create a function wrapped in a context that ignores warnings.
    """
	@functools.wraps(func)
	def new_func(*args, **kwargs):
		with warnings.catch_warnings():
			warnings.simplefilter('ignore')
			return func(*args, **kwargs)
	return new_func

class Description(six.text_type):
	"""A description with optional cross-references.
    """

	_RX_OBO_EXTRACTER = re.compile(r'[\"\'](.*)[\"\']( \[(.+)\])?')

	@classmethod
	def from_obo(cls, obo_header):
		match = cls._RX_OBO_EXTRACTER.search(obo_header)
		if match is not None:
			desc, _, xref = match.groups()
		else:
			raise ValueError("not a valid obo definition")
		if xref is not None:
			xref = [x.split(' ')[0] for x in xref.split(', ')]
		return cls(desc, xref)

	def __new__(cls, text, xref=None):
		return super(Description, cls).__new__(cls, text)

	def __init__(self, text, xref=None):
		self.xref = xref or []

	def __repr__(self):
		return "Description('{}', {})".format(self, self.xref)

	@property
	def obo(self):
		return 'def: "{}" [{}]'.format(
            self, ', '.join(self.xref)
        )


_obo_synonyms_map = {'exact_synonym': 'EXACT', 'broad_synonym': 'BROAD',
                    'narrow_synonym': 'NARROW', 'synonym': 'RELATED'}

class SynonymType(object):
	"""A synonym type in an ontology.

    Attributes:
        name(str): the name of the synonym type
        scope(str, optional): the scope all synonyms of
            that type will always have(either 'EXACT',
            'BROAD', 'NARROW', 'RELATED', or None).
        desc(Description): the description of the synonym type

    """

	__slots__ = ['name', 'desc', 'scope']
	_instances = collections.OrderedDict()
	_RX_OBO_EXTRACTER = re.compile(r'(?P<name>[^ ]*)[ ]*\"(?P<desc>.*)\"[ ]*(?P<scope>BROAD|NARROW|EXACT|RELATED)?')

	def __init__(self, name, desc, scope=None):
		"""Create a new synonym type.

        Arguments:
            name (str): the name of the synonym type.
            desc (str): the description of the synonym type.
            scope (str, optional): the scope modifier.
        """
		self.name = name
		self.desc = desc
		if scope in {'BROAD', 'NARROW', 'EXACT', 'RELATED', None}:
			self.scope = scope
		elif scope in {six.b('BROAD'), six.b('NARROW'), six.b('EXACT'), six.b('RELATED')}:
			self.scope = scope.decode('utf-8')
		else:
			raise ValueError("scope must be 'NARROW', 'BROAD', 'EXACT', 'RELATED' or None")
		self._register()

	def _register(self):
		self._instances[self.name] = self

	@classmethod
	def from_obo(cls, obo_header):
		if isinstance(obo_header, six.binary_type):
			obo_header = obo_header.decode('utf-8')

		groupdict = cls._RX_OBO_EXTRACTER.search(obo_header).groupdict()
		result = {k:v.strip() if v else None for k,v in six.iteritems(groupdict)}
		return cls(**result)

	@property
	def obo(self):
		"""str: the synonym type serialized in obo format.
        """
		return ' '.join(['synonymtypedef:', self.name,
                         '"{}"'.format(self.desc),
                         self.scope or '']).strip()

	@output_str
	def __repr__(self):
		return ''.join(['<SynonymType: ', self.name, ' ',
                        '"{}"'.format(self.desc),
                        ' {}>'.format(self.scope) \
                        if self.scope else '>']).strip()

	def __hash__(self):
		return hash((self.name, self.desc, self.scope))


class Synonym(object):
	"""A synonym in an ontology.
    """

	_RX_OBO_EXTRACTER = re.compile(r'\"(?P<desc>.*)\" *(?P<scope>EXACT|BROAD|NARROW|RELATED)? *(?P<syn_type>[^ ]+)? \[(?P<xref>.*)\]')

	def __init__(self, desc, scope=None, syn_type=None, xref=None):
		"""Create a new synonym.

        Arguments:
            desc (str): a description of the synonym.
            scope (str, optional): the scope of the synonym (either
                EXACT, BROAD, NARROW or RELATED).
            syn_type (SynonymType, optional): the type of synonym if
                relying on a synonym type defined in the *Typedef*
                section of the ontology.
            xref (list, optional): a list of cross-references for the
                synonym.

        """
		if isinstance(desc, six.binary_type):
			self.desc = desc.decode('utf-8')
		elif isinstance(desc, six.text_type):
			self.desc = desc
		else:
			raise ValueError("desc must be bytes or str, not {}".format(type(desc).__name__))

		if isinstance(scope, six.binary_type):
			self.scope = scope.decode('utf-8')
		elif isinstance(scope, six.text_type):
			self.scope = scope
		elif scope is None:
			self.scope = "RELATED"

		if syn_type is not None:
			try:
				self.syn_type = SynonymType._instances[syn_type]
				self.scope = self.syn_type.scope or self.scope or 'RELATED'
			except KeyError as e:
				raise ValueError("Undefined synonym type: {}".format(syn_type))
		else:
			self.syn_type = None

		if self.scope not in {'EXACT', 'BROAD', 'NARROW', 'RELATED', None}:
			raise ValueError("scope must be 'NARROW', 'BROAD', 'EXACT', 'RELATED' or None")

		self.xref = xref or []

	@classmethod
	def from_obo(cls, obo_header, scope='RELATED'):

		if isinstance(obo_header, six.binary_type):
			obo_header = obo_header.decode('utf-8')

		groupdict = cls._RX_OBO_EXTRACTER.search(obo_header).groupdict()
		if groupdict.get('xref', ''):
			groupdict['xref'] = [x.strip() for x in groupdict['xref'].split(',')]
		groupdict['syn_type'] = groupdict['syn_type'] or None

		return cls(**groupdict)

	@property
	def obo(self):
		"""str: the synonym serialized in obo format.
        """
		return 'synonym: "{}" {} [{}]'.format(
            self.desc,
            ' '.join([self.scope, self.syn_type.name])\
                if self.syn_type else self.scope,
            ', '.join(self.xref)
        )

	@output_str
	def __repr__(self):
		return '<Synonym: "{}" {} [{}]>'.format(
            self.desc,
            ' '.join([self.scope, self.syn_type.name])\
                if self.syn_type else self.scope,
            ', '.join(self.xref)
        )

	def __eq__(self, other):
		return self.desc==other.desc and self.scope==other.scope and self.syn_type==other.syn_type and self.xref==other.xref

	def __hash__(self):
		return hash((self.desc, self.scope, self.syn_type, tuple(self.xref)))

class OboParser(BaseParser):

	extensions = (".obo", ".obo.gz")

	@classmethod
	def hook(cls, force=False, path=None, lookup=None):
		"""Test whether this parser should be used.

        The current behaviour relies on filenames, file extension
        and looking ahead a small buffer in the file object.

        """
		if force:
			return True
		elif path is not None and path.endswith(cls.extensions):
			return True
		elif lookup is not None and lookup.startswith(b'format-version:'):
			return True
		return False

	@classmethod
	def parse(cls, stream):  # noqa: D102

		_section    = OboSection.meta
		meta        = collections.defaultdict(list)
		_rawterms   = []
		_rawtypedef = []

		_term_parser = cls._parse_term(_rawterms)
		next(_term_parser)

		for streamline in stream:

			# manage encoding && cleaning of line
			streamline = streamline.decode('utf-8')
			if streamline[0] in string.whitespace:
				continue
			elif streamline[0] == "[":
				_section = cls._check_section(streamline, _section)

			if _section is OboSection.meta:
				cls._parse_metadata(streamline, meta)
			elif _section is OboSection.typedef:
				cls._parse_typedef(streamline, _rawtypedef)
			elif _section is OboSection.term:
				_term_parser.send(streamline)

		terms = cls._classify(_rawtypedef, _rawterms)
		imports = set(meta['import']) if 'import' in meta else set()

		return dict(meta), terms, imports

	@staticmethod
	def _check_section(line, section):
		"""Update the section being parsed.

        The parser starts in the `OboSection.meta` section but once
        it reaches the first ``[Typedef]``, it will enter the
        `OboSection.typedef` section, and/or when it reaches the first
        ``[Term]``, it will enter the `OboSection.term` section.

        """
		if "[Term]" in line:
			section = OboSection.term
		elif "[Typedef]" in line:
			section = OboSection.typedef
		return section

	@classmethod
	def _parse_metadata(cls, line, meta, parse_remarks=True):
		"""Parse a metadata line.

        The metadata is organized as a ``key: value`` statement which
        is split into the proper key and the proper value.

        Arguments:
            line (str): the line containing the metadata
            parse_remarks(bool, optional): set to `False` to avoid
                parsing the remarks.

        Note:
            If the line follows the following schema:
            ``remark: key: value``, the function will attempt to extract
            the proper key/value instead of leaving everything inside
            the remark key.

            This may cause issues when the line is identified as such
            even though the remark is simply a sentence containing a
            colon,  such as ``remark: 090506 "Attribute"`` in Term
            deleted and new entries: Scan Type [...]"
            (found in imagingMS.obo). To prevent the splitting from
            happening, the text on the left of the colon must be less
            that *20 chars long*.

        """
		key, value = line.split(':', 1)
		key, value = key.strip(), value.strip()
		if parse_remarks and "remark" in key:                        # Checking that the ':' is not
			if 0<value.find(': ')<20:                                # not too far avoid parsing a sentence
				try:                                                 # containing a ':' as a key: value
					cls._parse_metadata(value, meta, parse_remarks)  # obo statement nested in a remark
				except ValueError:                                   # (20 is arbitrary, it may require
					pass                                             # tweaking)
		else:
			meta[key].append(value)
			try:
				syn_type_def = []
				for m in meta['synonymtypedef']:
					if not isinstance(m, SynonymType):
						x = SynonymType.from_obo(m)
						syn_type_def.append(x)
					else:
						syn_type_def.append(m)
			except KeyError:
				pass
			else:
				meta['synonymtypedef'] = syn_type_def

	@staticmethod
	def _parse_typedef(line, _rawtypedef):
		"""Parse a typedef line.

        The typedef is organized as a succesion of ``key:value`` pairs
        that are extracted into the same dictionnary until a new
        header is encountered

        Arguments:
            line (str): the line containing a typedef statement
        """
		if "[Typedef]" in line:
			_rawtypedef.append(collections.defaultdict(list))
		else:
			key, value = line.split(':', 1)
			_rawtypedef[-1][key.strip()].append(value.strip())

	@staticmethod
	def _parse_term(_rawterms):
		"""Parse a term line.

        The term is organized as a succesion of ``key:value`` pairs
        that are extracted into the same dictionnary until a new
        header is encountered

        Arguments:
            line (str): the line containing a term statement
        """
		line = yield
		_rawterms.append(collections.defaultdict(list))
		while True:
			line = yield
			if "[Term]" in line:
				_rawterms.append(collections.defaultdict(list))
			else:
				key, value = line.split(':', 1)
				_rawterms[-1][key.strip()].append(value.strip())
			#_rawterms

	@staticmethod
	def _classify(_rawtypedef, _rawterms):
		"""Create proper objects out of extracted dictionnaries.

        New Relationship objects are instantiated with the help of
        the `Relationship._from_obo_dict` alternate constructor.

        New `Term` objects are instantiated by manually extracting id,
        name, desc and relationships out of the ``_rawterm``
        dictionnary, and then calling the default constructor.
        """
		terms = collections.OrderedDict()
		_cached_synonyms = {}

		for _typedef in _rawtypedef:
			Relationship._from_obo_dict( # instantiate a new Relationship
                {k:v for k,lv in six.iteritems(_typedef) for v in lv}
            )


		for _term in _rawterms:
			synonyms = set()

			_id   = _term['id'][0]
			_name = _term.pop('name', ('',))[0]
			_desc = _term.pop('def', ('',))[0]

			_relations = collections.defaultdict(list)
			try:
				for other in _term.get('is_a', ()):
					_relations[Relationship('is_a')].append(other.split('!')[0].strip())
			except IndexError:
				pass
			try:
				for relname, other in ( x.split(' ', 1) for x in _term.pop('relationship', ())):
					_relations[Relationship(relname)].append(other.split('!')[0].strip())
			except IndexError:
				pass

			for key, scope in six.iteritems(_obo_synonyms_map):
				for obo_header in _term.pop(key, ()):
					try:
						s = _cached_synonyms[obo_header]
					except KeyError:
						s = Synonym.from_obo(obo_header, scope)
						_cached_synonyms[obo_header] = s
					finally:
						synonyms.add(s)

			desc = Description.from_obo(_desc) if _desc else Description("")

			terms[_id] = Term(_id, _name, desc, dict(_relations), synonyms, dict(_term))
		return terms


OboParser()

RDF_ABOUT = "{{{}}}{}".format(owl_ns['rdf'], 'about')
RDF_RESOURCE = "{{{}}}{}".format(owl_ns['rdf'], 'resource')
RDF_DATATYPE = "{{{}}}{}".format(owl_ns['rdf'], 'datatype')
OWL_AXIOM = "{{{}}}{}".format(owl_ns['owl'], 'Axiom')
OWL_CLASS = "{{{}}}{}".format(owl_ns['owl'], 'Class')
OWL_ONTOLOGY = "{{{}}}{}".format(owl_ns['owl'], 'Ontology')

class OwlXMLParser(BaseParser):
	"""An OwlXML Parser.

    Provides functions common to all OwlXMLParsers, such as a
    function to extract ontology terms id from a url, or the common
    `~OwlXMLParser.hook` method.
    """

	ns = owl_ns
	extensions = ('.owl', '.ont', '.owl.gz', '.ont.gz')

	@classmethod
	def hook(cls, force=False, path=None, lookup=None):  # noqa: D102
		if force:
			return True
		if path is not None and path.endswith(cls.extensions):
			return True
		if lookup is not None and lookup.startswith(b'<?xml'):
			return True
		return False

	@classmethod
	@nowarnings
	def parse(cls, stream):  # noqa: D102
		tree = etree.parse(stream, parser = etree.XMLParser(huge_tree=True)) # parser added for a very big file!!!

		meta = cls._extract_resources(tree.find(OWL_ONTOLOGY))
		terms = collections.OrderedDict()

		for rawterm in cls._iter_rawterms(tree):
			term = Term(
                rawterm.pop('id'),
                rawterm.pop('label', [''])[0],
                rawterm.pop('definition', '') or rawterm.pop('IAO_0000115', ''),
                cls._extract_obo_relation(rawterm),
                cls._extract_obo_synonyms(rawterm),
                cls._relabel_to_obo(rawterm),
            )
			terms[term.id] = term
			# TODO: extract axioms through targeted XPaths

		terms = cls._annotate(terms, tree)
		meta = cls._relabel_to_obo(meta)
		meta.setdefault('imports', [])

		return meta, terms, set(meta['imports'])

	@classmethod
	def _annotate(cls, terms, tree):

		for axiom in map(cls._extract_resources, tree.iterfind(OWL_AXIOM)):

			if not 'annotatedSource' in axiom:
				continue

			prop = cls._get_id_from_url(axiom['annotatedProperty'][0])
			src = cls._get_id_from_url(axiom['annotatedSource'][0])
			target = axiom.get('annotatedTarget')

			# annotated description with xrefs
			if prop == 'IAO:0000115':
				if src in terms:
					terms[src].desc = Description(
                        ''.join(target or []), axiom.get('hasDbXref', [])
                    )

		return terms



	@staticmethod
	def _get_basename(tag):
		"""Remove the namespace part of the tag.
        """
		return tag.split('}', 1)[-1]

	@staticmethod
	def _get_id_from_url(url):
		"""Extract the ID of a term from an XML URL.
        """
		_id = url.split('#' if '#' in url else '/')[-1]
		return _id.replace('_', ':')

	@staticmethod
	def _extract_resources(elem):
		"""Extract the children of an element as a key/value mapping.
        """
		resources = collections.defaultdict(list)
		for child in itertools.islice(elem.iter(), 1, None):
			try:
				basename = child.tag.split('}', 1)[-1]
				if child.text is not None:
					child.text = child.text.strip()
				if child.text:
					resources[basename].append(child.text)
				elif child.get(RDF_RESOURCE) is not None:
					resources[basename].append(child.get(RDF_RESOURCE))
			except AttributeError:
				pass
		return dict(resources)

	@classmethod
	def _iter_rawterms(cls, tree):
		"""Iterate through the raw terms (Classes) in the ontology.
        """
		for elem in tree.iterfind(OWL_CLASS):
			if RDF_ABOUT not in elem.keys():   # This avoids parsing a class
				continue                       # created by restriction
			rawterm = cls._extract_resources(elem)
			rawterm['id'] = cls._get_id_from_url(elem.get(RDF_ABOUT))
			yield rawterm

	@staticmethod
	def _extract_obo_synonyms(rawterm):
		"""Extract the synonyms defined in the rawterm.
        """
		synonyms = set()
		# keys in rawterm that define a synonym
		keys = set(owl_synonyms).intersection(rawterm.keys())
		for k in keys:
			for s in rawterm[k]:
				synonyms.add(Synonym(s, owl_synonyms[k]))
		return synonyms

	@classmethod
	def _extract_obo_relation(cls, rawterm):
		"""Extract the relationships defined in the rawterm.
        """
		relations = {}
		if 'subClassOf' in rawterm:
			relations[Relationship('is_a')] = l = []
			l.extend(map(cls._get_id_from_url, rawterm.pop('subClassOf')))
		return relations

	@staticmethod
	def _relabel_to_obo(d):
		"""Change the keys of ``d`` to use Obo labels.
		"""
		return {
            owl_to_obo.get(old_k, old_k): old_v
                for old_k, old_v in six.iteritems(d)
        }

class Term(object):
	"""A term in an ontology.

    Example:
        >>> ms = Ontology('tests/resources/psi-ms.obo')
        >>> type(ms['MS:1000015'])
        <class 'pronto.term.Term'>

    """

	__slots__ = ['id', 'name', 'desc', 'relations', 'other', 'synonyms',
                 '_children', '_parents', '_rchildren', '_rparents',
                 '__weakref__']

	def __init__(self, id, name='', desc='', relations=None, synonyms=None, other=None):
		"""Create a new Term.

        Arguments:
            id (str): the Term id (e.g. "MS:1000031")
            name (str): the name of the Term in human language
            desc (str): a description of the Term
            relations (dict, optional): a dictionary containing the other
                terms the Term is in a relationship with.
            other (dict, optional): other information about the term
            synonyms (set, optional): a list containing :obj:`pronto.synonym.Synonym`
                objects relating to the term.

        Example:
            >>> new_term = Term('TR:001', 'new term', 'a new term')
            >>> linked_term = Term('TR:002', 'other new', 'another term',
            ...                    { Relationship('is_a'): 'TR:001'})

        """
		if not isinstance(id, six.text_type):
			id = id.decode('utf-8')
		if isinstance(desc, six.binary_type):
			desc = desc.decode('utf-8')
		if not isinstance(desc, Description):
			desc = Description(desc)
		if not isinstance(name, six.text_type):
			name = name.decode('utf-8')

		self.id = id
		self.name = name
		self.desc = desc
		self.relations = relations or {}
		self.other = other or {}
		self.synonyms = synonyms or set()

		self._rchildren  = {}
		self._rparents = {}
		self._children = None
		self._parents = None

	@output_str
	def __repr__(self):
		return "<{}: {}>".format(self.id, self.name)

	@property
	def parents(self):
		"""~TermList: The direct parents of the `Term`.
        """
		if self._parents is None:
			bottomups = tuple(Relationship.bottomup())

			self._parents = TermList()
			self._parents.extend(
                [ other
                    for rship,others in six.iteritems(self.relations)
                        for other in others
                            if rship in bottomups
                ]

            )

		return self._parents

	@property
	def children(self):
		"""~TermList: The direct children of the `Term`.
        """
		if self._children is None:
			topdowns = tuple(Relationship.topdown())
			self._children = TermList()
			self._children.extend(
                [ other
                    for rship,others in six.iteritems(self.relations)
                        for other in others
                            if rship in topdowns
                ]
            )
		return self._children

	@property
	@output_str
	def obo(self):
		"""str: the `Term` serialized in an Obo ``[Term]`` stanza.

        Note:
            The following guide was used:
            ftp://ftp.geneontology.org/pub/go/www/GO.format.obo-1_4.shtml
        """
		def add_tags(stanza_list, tags):
			for tag in tags:
				if tag in self.other:
					if isinstance(self.other[tag], list):
						for attribute in self.other[tag]:
							stanza_list.append("{}: {}".format(tag, attribute))
					else:
						stanza_list.append("{}: {}".format(tag, self.other[tag]))

		# metatags = ["id", "is_anonymous", "name", "namespace","alt_id", "def","comment",
		#             "subset","synonym","xref","builtin","property_value","is_a",
		#             "intersection_of","union_of","equivalent_to","disjoint_from",
		#             "relationship","created_by","creation_date","is_obsolete",
		#             "replaced_by", "consider"]

		stanza_list = ["[Term]"]

		# id
		stanza_list.append("id: {}".format(self.id))


		# name
		if self.name is not None:
			stanza_list.append("name: {}".format(self.name))
		else:
			stanza_list.append("name: ")

		add_tags(stanza_list, ['is_anonymous', 'alt_id'])

		# def
		if self.desc:
			stanza_list.append(self.desc.obo)

		# comment, subset
		add_tags(stanza_list, ['comment', 'subset'])

		# synonyms
		for synonym in sorted(self.synonyms, key=str):
			stanza_list.append(synonym.obo)

		add_tags(stanza_list, ['xref'])

		# is_a
		if Relationship('is_a') in self.relations:
			for companion in self.relations[Relationship('is_a')]:
				stanza_list.append("is_a: {} ! {}".format(companion.id, companion.name))

		add_tags(stanza_list, ['intersection_of', 'union_of', 'disjoint_from'])

		for relation in self.relations:
			if relation.direction=="bottomup" and relation is not Relationship('is_a'):
				stanza_list.extend(
                    "relationship: {} {} ! {}".format(
                        relation.obo_name, companion.id, companion.name
                    ) for companion in self.relations[relation]
                )

		add_tags(stanza_list, ['is_obsolete', 'replaced_by', 'consider',
                               'builtin', 'created_by', 'creation_date'])

		return "\n".join(stanza_list)

	@property
	def __deref__(self):
		"""dict: the `Term` as a `dict` without circular references.
        """
		return {
            'id': self.id,
            'name': self.name,
            'other': self.other,
            'desc': self.desc,
            'relations': {k.obo_name:v.id for k,v in six.iteritems(self.relations)}
         }

	def __getstate__(self):
		return (
            self.id,
            self.name,
            tuple((k,v) for k,v in six.iteritems(self.other)),
            self.desc,
            tuple((k.obo_name,v.id) for k,v in six.iteritems(self.relations)),
            frozenset(self.synonyms),
        )

	def __setstate__(self, state):
		self.id = state[0]
		self.name = state[1]
		self.other = {k:v for (k,v) in state[2]}
		self.desc = state[3]
		self.relations = {Relationship(k):v for k,v in state[4]}
		self.synonyms = set(state[5])
		self._empty_cache()

	def _empty_cache(self):
		"""Empty the cache of the Term's memoized functions.
        """
		self._children, self._parents = None, None
		self._rchildren, self._rparents = {}, {}

	def rchildren(self, level=-1, intermediate=True):
		"""Create a recursive list of children.

        Parameters:
            level (int): The depth level to continue fetching children from
                (default is -1, to get children to the utter depths)
            intermediate (bool): Also include the intermediate children
                (default is True)

        Returns:
            :obj:`pronto.TermList`:
            The recursive children of the Term following the parameters

        """
		try:
			return self._rchildren[(level, intermediate)]

		except KeyError:

			rchildren = []

			if self.children and level:

				if intermediate or level==1:
				    rchildren.extend(self.children)

				for child in self.children:
				    rchildren.extend(child.rchildren(level=level-1,
				                                     intermediate=intermediate))

			rchildren = TermList(unique_everseen(rchildren))
			self._rchildren[(level, intermediate)] = rchildren
			return rchildren

	def rparents(self, level=-1, intermediate=True):
		"""Create a recursive list of children.

        Note that the :param:`intermediate` can be used to include every
        parents to the returned list, not only the most nested ones.

        Parameters:
            level (int): The depth level to continue fetching parents from
                (default is -1, to get parents to the utter depths)
            intermediate (bool): Also include the intermediate parents
                (default is True)

        Returns:
            :obj:`pronto.TermList`:
            The recursive children of the Term following the parameters

        """
		try:
			return self._rparents[(level, intermediate)]

		except KeyError:

			rparents = []

			if self.parents and level:

				if intermediate or level==1:
				    rparents.extend(self.parents)

				for parent in self.parents:
				    rparents.extend(parent.rparents(level=level-1,
				                                     intermediate=intermediate))

			rparents = TermList(unique_everseen(rparents))
			self._rparents[(level, intermediate)] = rparents
			return rparents


class TermList(list):
	"""A list of `Term` instances.

    TermList behaves exactly like a list, except it contains shortcuts to
    generate lists of terms' attributes.

    Example:
        >>> nmr = Ontology('tests/resources/nmrCV.owl')
        >>> type(nmr['NMR:1000031'].children)
        <class 'pronto.term.TermList'>

        >>> nmr['NMR:1000031'].children.id
        [u'NMR:1000122', u'NMR:1000156', u'NMR:1000157', u'NMR:1000489']
        >>> nmr['NMR:1400014'].relations[Relationship('is_a')]
        [<NMR:1400011: cardinal part of NMR instrument>]


    .. tip::
        It is also possible to call Term methods on a TermList to
        create another TermList::

            >>> nmr['NMR:1000031'].rchildren(3, False).rparents(3, False).id
            [u'NMR:1000031']

    """

	def __init__(self, elements=None):
		"""Create a new `TermList`.

        Arguments:
            elements (collections.Iterable, optional): an Iterable
                that yields `Term` objects.

        Raises:
            TypeError: when the given ``elements`` are not instances
                of `Term`.

        """
		super(TermList, self).__init__()
		self._contents = set()
		try:
			for t in elements or []:
				super(TermList, self).append(t)
				self._contents.add(t.id)
		except AttributeError:
			raise TypeError('TermList can only contain Terms.')

	def append(self, element):
		if element not in self:
		    super(TermList, self).append(element)
		    try:
		        self._contents.add(element.id)
		    except AttributeError:
		        self._contents.add(element)

	def extend(self, sequence):
		for element in sequence:
		    self.append(element)

	def rparents(self, level=-1, intermediate=True):
		return TermList(unique_everseen(
            y for x in self for y in x.rparents(level, intermediate)
        ))

	def rchildren(self, level=-1, intermediate=True):
		return TermList(unique_everseen(
            y for x in self for y in x.rchildren(level, intermediate)
        ))

	@property
	def children(self):
		"""~TermList: the children of all the terms in the list.
        """
		return TermList(unique_everseen(
            y for x in self for y in x.children
        ))

	@property
	def parents(self):
		"""~TermList: the parents of all the terms in the list.
        """
		return TermList(unique_everseen(
            y for x in self for y in x.parents
        ))

	@property
	def id(self):
		"""list: a list of id corresponding to each term of the list.
        """
		return [x.id for x in self]

	@property
	def name(self):
		"""list: the name of all the terms in the list.
        """
		return [x.name for x in self]

	@property
	def desc(self):
		"""list: the description of all the terms in the list.
        """
		return [x.desc for x in self]

	@property
	def other(self):
		"""list: the "other" property of all the terms in the list.
        """
		return [x.other for x in self]

	@property
	def obo(self):
		"""list: all the terms in the term list serialized in obo.
        """
		return [x.obo for x in self]

	def __getstate__(self):
		return tuple(x for x in self)

	def __setstate__(self, state):
		pass

	def __contains__(self, term):
		"""Check if the TermList contains a term.

        The method allows to check for the presence of a Term in a
        TermList based on a Term object or on a term accession number.

        Example:

            >>> from pronto import *
            >>> nmr = Ontology('tests/resources/nmrCV.owl')
            >>> 'NMR:1000122' in nmr['NMR:1000031'].children
            True
            >>> nmr['NMR:1000122'] in nmr['NMR:1000031'].children
            True

        """
		try:
			_id = term.id
		except AttributeError:
			_id = term
		return _id in self._contents


# coding: utf-8
"""Definition of the `Relationship` class.
"""
class Relationship(object):
	"""A Relationship object.

    The Relationship class actually behaves as a factory, creating new
    relationships via the default Python syntax only if no relationship
    of the same name are present in the class py:attribute:: _instances
    (a dictionnary containing memoized relationships).


    Note:
       Relationships are pickable and always refer to the same adress even
       after being pickled and unpickled, but that requires to use at least
       pickle protocol 2 (which is not default on Python 2, so take care !)::

          >>> import pronto
          >>> import io, pickle
          >>>
          >>> src = io.BytesIO()
          >>> p = pickle.Pickler(src, pickle.HIGHEST_PROTOCOL)
          >>>
          >>> isa = pronto.Relationship('is_a')
          >>> isa_id = id(isa)
          >>>
          >>> p.dump(isa)
          >>> dst = io.BytesIO(src.getvalue())
          >>>
          >>> u = pickle.Unpickler(dst)
          >>> new_isa = u.load()
          >>>
          >>> id(new_isa) == isa_id
          True
          >>> # what's that black magic ?!

    """

	_instances = collections.OrderedDict()

	def __init__(self, obo_name, symmetry=None, transitivity=None,
                 reflexivity=None, complementary=None, prefix=None,
                 direction=None, comment=None, aliases=None):
		"""Instantiate a new relationship.

        Arguments:
            obo_name (str): the name of the relationship as it appears
                in obo files (such as is_a, has_part, etc.)
            symetry (bool or None): the symetry of the relationship
            transitivity (bool or None): the transitivity of the relationship.
            reflexivity (bool or None): the reflexivity of the relationship.
            complementary (string or None): if any, the obo_name of the
                complementary relationship.
            direction (string, optional): if any, the direction of the
                relationship (can be 'topdown', 'bottomup', 'horizontal').
                A relationship with a direction set as 'topdown' will be
                counted as _childhooding_ when acessing `Term.children`.
            comment (string, optional): comments about the relationship.
            aliases (list, optional): a list of names that are synonyms to
                the obo name of this relationship.

        Note:
            For symetry, transitivity, reflexivity, the allowed values are
            the following:

            * `True` for reflexive, transitive, symmetric
            * `False` for areflexive, atransitive, asymmetric
            * `None` for non-reflexive, non-transitive, non-symmetric

        """
		if obo_name not in self._instances:
			if not isinstance(obo_name, six.text_type):
				obo_name = obo_name.decode('utf-8')
			if complementary is not None and not isinstance(complementary, six.text_type):
				complementary = complementary.decode('utf-8')
			if prefix is not None and not isinstance(prefix, six.text_type):
				prefix = prefix.decode('utf-8')
			if direction is not None and not isinstance(direction, six.text_type):
				direction = direction.decode('utf-8')
			if comment is not None and not isinstance(comment, six.text_type):
				comment = comment.decode('utf-8')

			self.obo_name = obo_name
			self.symmetry = symmetry
			self.transitivity = transitivity
			self.reflexivity = reflexivity
			self.complementary = complementary or ''
			self.prefix = prefix or ''
			self.direction = direction or ''
			self.comment = comment or ''
			if aliases is not None:
				self.aliases = [alias.decode('utf-8') if not isinstance(alias, six.text_type) else alias for alias in aliases]
			else:
				self.aliases = []

			self._instances[obo_name] = self
			for alias in self.aliases:
				self._instances[alias] = self

	def complement(self):
		"""Return the complementary relationship of self.

        Raises:
            ValueError: if the relationship has a complementary
                which was not defined.

        Returns:
            complementary (Relationship): the complementary relationship.

        Example:

            >>> from pronto.relationship import Relationship
            >>> print(Relationship('has_part').complement())
            Relationship('part_of')
            >>> print(Relationship('has_units').complement())
            None

        """
		if self.complementary:
			#if self.complementary in self._instances.keys():
			try:
				return self._instances[self.complementary]
			except KeyError:
				raise ValueError('{} has a complementary but it was not defined !')

		else:
			return None

	@output_str
	def __repr__(self):
		"""Return a string reprensentation of the relationship.
        """
		return "Relationship('{}')".format(self.obo_name)

	def __new__(cls, obo_name, *args, **kwargs):
		"""Create a relationship or returning an already existing one.

        This allows to do the following:

            >>> Relationship('has_part').direction
            u'topdown'

        The Python syntax is overloaded, and what looks like a object
        initialization in fact retrieves an existing object with all its
        properties already set. The Relationship class behaves like a
        factory of its own objects !

        Todo:
            * Add a warning for unknown relationship (the goal being to
              instantiate every known ontology relationship and even
              allow instatiation of file-defined relationships).

        """
		if obo_name in cls._instances:
			return cls._instances[obo_name]
		else:
			return super(Relationship, cls).__new__(cls)

	@classmethod
	def topdown(cls):
		"""Get all topdown `Relationship` instances.

        Returns:
            :obj:`generator`

        Example:

            >>> from pronto import Relationship
            >>> for r in Relationship.topdown():
            ...    print(r)
            Relationship('can_be')
            Relationship('has_part')

        """
		return tuple(unique_everseen(r for r in cls._instances.values() if r.direction=='topdown'))

	@classmethod
	def bottomup(cls):
		"""Get all bottomup `Relationship` instances.

        Example:

            >>> from pronto import Relationship
            >>> for r in Relationship.bottomup():
            ...    print(r)
            Relationship('is_a')
            Relationship('part_of')

        """
		return tuple(unique_everseen(r for r in cls._instances.values() if r.direction=='bottomup'))

	def __getnewargs__(self):
		return (self.obo_name,)

	@classmethod
	def _from_obo_dict(cls, d):

		if d['id'] in cls._instances:
			return cls._instances[d['id']]
		try:
			complementary = d['inverse_of']
		except KeyError:
			complementary = ""

		try:
			transitivity = d['is_transitive'].lower() == "true"
		except KeyError:
			transitivity = None

		try:
			symmetry = d['is_symmetric'].lower() == "true"
		except KeyError:
			symmetry = None

		try:
			reflexivity = d['is_reflexive'].lower() == "true"
		except KeyError:
			reflexivity = None

		try:
			symmetry = d['is_antisymetric'].lower() == "false"
		except KeyError:
			pass

		return Relationship(d['id'], symmetry=symmetry, transitivity=transitivity,
                            reflexivity=reflexivity, complementary=complementary)



Relationship('is_a', symmetry=False, transitivity=True,
                    reflexivity=True, complementary='can_be',
                    direction='bottomup')

Relationship('can_be', symmetry=False, transitivity=True,
                    reflexivity=True, complementary='is_a',
                    direction='topdown')

Relationship('has_part', symmetry=False, transitivity=True,
                        reflexivity=True, complementary='part_of',
                        direction='topdown')

Relationship('part_of', symmetry=False, transitivity=True,
                        reflexivity=True, complementary='has_part',
                        direction='bottomup', aliases=['is_part'])

Relationship('has_units', symmetry=False, transitivity=False,
                          reflexivity=None)

Relationship('has_domain', symmetry=False, transitivity=False)

class Ontology(collections.Mapping):
	"""An ontology.

    Ontologies inheriting from this class will be able to use the same API as
    providing they generated the expected structure in the :func:`_parse`
    method.

    Attributes:
        meta (dict): the metatada contained in the `Ontology`.
        terms (dict): the terms of the ontology. Not very useful to
            access directly, since `Ontology` provides many useful
            shortcuts and features to access them.
        imports (list): a list of paths and/or URLs to additional
            ontologies the ontology depends on.
        path (str, optional): the path to the ontology, if any.


    Examples:
        Import an ontology from a remote location::

            >>> from pronto import Ontology
            >>> envo = Ontology("http://purl.obolibrary.org/obo/bfo.owl")

        Merge two local ontologies and export the merge::

            >>> uo = Ontology("tests/resources/uo.obo", False)
            >>> cl = Ontology("tests/resources/cl.ont.gz", False)
            >>> uo.merge(cl)
            >>> with open('tests/run/merge.obo', 'w') as f:
            ...     f.write(uo.obo) # doctest: +SKIP

        Export an ontology with its dependencies embedded::

            >>> cl = Ontology("tests/resources/cl.ont.gz")
            >>> with open('tests/run/cl.obo', 'w') as f:
            ...     f.write(cl.obo) # doctest: +SKIP

        Use the parser argument to force usage a parser::

            >>> cl = Ontology("tests/resources/cl.ont.gz",
            ...               parser='OwlXMLParser')

	"""

	__slots__ = ("path", "meta", "terms", "imports", "_parsed_by")

	def __init__(self, handle=None, imports=True, import_depth=-1, timeout=2, parser=None):
		"""Create an `Ontology` instance from a file handle or a path.

        Arguments:
            handle (io.IOBase or str): the location of the file (either
                a path on the local filesystem, or a FTP or HTTP URL),
                a readable file handle containing an ontology, or `None`
                to create a new ontology from scratch.
            imports (bool, optional): if `True` (the default), embed the
                ontology imports into the returned instance.
            import_depth (int, optional): The depth up to which the
                imports should be resolved. Setting this to 0 is
                equivalent to setting ``imports`` to `False`. Leave
                as default (-1) to handle all the imports.
            timeout (int, optional): The timeout in seconds for network
                operations.
            parser (~pronto.parser.BaseParser, optional): A parser
                instance to use. Leave to `None` to autodetect.

        """
		self.meta = {}
		self.terms = {}
		self.imports = ()
		self._parsed_by = None

		if handle is None:
			self.path = None
		elif hasattr(handle, 'read'):
			self.path = getattr(handle, 'name', None) \
                     or getattr(handle, 'url', None) \
                     or getattr(handle, 'geturl', lambda: None)()
			self.parse(handle, parser)
		elif isinstance(handle, six.string_types):
			self.path = handle
			with self._get_handle(handle, timeout) as handle:
				self.parse(handle, parser)
		else:
			actual = type(handle).__name__
			raise TypeError("Invalid type for 'handle': expected None, file "
                            "handle or string, found {}".format(actual))

		if handle is not None and self._parsed_by is None:
			raise ValueError("Could not find a suitable parser to parse {}".format(handle))

		self.adopt()
		self.resolve_imports(imports, import_depth, parser)
		self.reference()

	def __repr__(self):
		if self.path is not None:
			return "Ontology(\"{}\")".format(self.path)
		return super(Ontology, self).__repr__()

	def __contains__(self, item):
		"""Check if the ontology contains a term.

        It is possible to check if an Ontology contains a Term
        using an id or a Term instance.

        Raises:
            TypeError: if argument (or left operand) is
                neither a string nor a Term

        Example:
            >>> 'CL:0002404' in cl
            True
            >>> from pronto import Term
            >>> Term('TST:001', 'tst') in cl
            False

		"""
		if isinstance(item, six.string_types):
			return item in self.terms
		elif isinstance(item, Term):
			return item.id in self.terms
		else:
			raise TypeError("'in <Ontology>' requires string or Term as left "
                            "operand, not {}".format(type(item)))

	def __iter__(self):
		"""Return an iterator over the Terms of the Ontology.

        For convenience of implementation, the returned instance is
        actually a generator that yields each term of the ontology,
        sorted in the definition order in the ontology file.

        Example:
            >>> for k in uo:
            ...    if 'basepair' in k.name:
            ...       print(k)
            <UO:0000328: kilobasepair>
            <UO:0000329: megabasepair>
            <UO:0000330: gigabasepair>
		"""
		return six.itervalues(self.terms)

	def __getitem__(self, item):
		"""Get a term in the `Ontology`.

        Method was overloaded to allow accessing to any Term of the
        `Ontology` using the Python dictionary syntax.

        Example:
            >>> cl['CL:0002380']
            <CL:0002380: oospore>
            >>> cl['CL:0002380'].relations
            {Relationship('is_a'): [<CL:0000605: fungal asexual spore>]}

		"""
		return self.terms[item]

	def __len__(self):
		"""Return the number of terms in the Ontology.
		"""
		return len(self.terms)

	def __getstate__(self):
		meta = frozenset( (k, frozenset(v)) for k,v in six.iteritems(self.meta) )
		imports = self.imports
		path = self.path
		terms = frozenset(term for term in self)
		return (meta, imports, path, terms)

	def __setstate__(self, state):
		self.meta = {k:list(v) for (k,v) in state[0] }
		self.imports = state[1]
		self.path = state[2]
		self.terms = {t.id:t for t in state[3]}
		self.reference()

	def parse(self, stream, parser=None):
		"""Parse the given file using available `BaseParser` instances.

        Raises:
            TypeError: when the parser argument is not a string or None.
            ValueError: when the parser argument is a string that does
                not name a `BaseParser`.

		"""
		force, parsers = self._get_parsers(parser)

		try:
			stream.seek(0)
			lookup = stream.read(1024)
			stream.seek(0)
		except (io.UnsupportedOperation, AttributeError):
			lookup = None

		for p in parsers:
			if p.hook(path=self.path, force=force, lookup=lookup):
				self.meta, self.terms, self.imports = p.parse(stream)
				self._parsed_by = p.__name__
				break

	def _get_parsers(self, name):
		"""Return the appropriate parser asked by the user.

        Todo:
            Change `Ontology._get_parsers` behaviour to look for parsers
            through a setuptools entrypoint instead of mere subclasses.
		"""

		parserlist = BaseParser.__subclasses__()
		forced = name is None

		if isinstance(name, (six.text_type, six.binary_type)):
			parserlist = [p for p in parserlist if p.__name__ == name]
			if not parserlist:
				raise ValueError("could not find parser: {}".format(name))

		elif name is not None:
			raise TypeError("parser must be {types} or None, not {actual}".format(
                types=" or ".join([six.text_type.__name__, six.binary_type.__name__]),
                actual=type(parser).__name__,
            ))

		return not forced, parserlist


	def adopt(self):
		"""Make terms aware of their children.

        This is done automatically when using the `~Ontology.merge` and
        `~Ontology.include` methods as well as the `~Ontology.__init__`
        method, but it should be called in case of manual editing of the
        parents or children of a `Term`.

		"""
		valid_relationships = set(Relationship._instances.keys())

		relationships = [
            (parent, relation.complement(), term.id)
                for term in six.itervalues(self.terms)
                    for relation in term.relations
                        for parent in term.relations[relation]
                            if relation.complementary
                                and relation.complementary in valid_relationships
        ]

		relationships.sort(key=operator.itemgetter(2))

		for parent, rel, child in relationships:
			if rel is None:
				break

			try:
				parent = parent.id
			except AttributeError:
				pass

			if parent in self.terms:
				try:
					if child not in self.terms[parent].relations[rel]:
						self.terms[parent].relations[rel].append(child)
				except KeyError:
					self[parent].relations[rel] = [child]

		del relationships

	def reference(self):
		"""Make relations point to ontology terms instead of term ids.

        This is done automatically when using the :obj:`merge` and :obj:`include`
        methods as well as the :obj:`__init__` method, but it should be called in
        case of manual changes of the relationships of a Term.
		"""
		for termkey, termval in six.iteritems(self.terms):
			termval.relations.update(
                (relkey, TermList(
                    (self.terms.get(x) or Term(x, '', '')
                    if not isinstance(x, Term) else x) for x in relval
                )) for relkey, relval in six.iteritems(termval.relations)
            )

	def resolve_imports(self, imports, import_depth, parser=None):
		"""Import required ontologies.
		"""
		if imports and import_depth:
			for i in list(self.imports):
				try:

					if os.path.exists(i) or i.startswith(('http', 'ftp')):
						self.merge(Ontology(i, import_depth=import_depth-1, parser=parser))

					else: # try to look at neighbouring ontologies
						self.merge(Ontology( os.path.join(os.path.dirname(self.path), i),
                                             import_depth=import_depth-1, parser=parser))

				except (IOError, OSError, URLError, HTTPError, _etree.ParseError) as e:
					warnings.warn("{} occured during import of "
                                  "{}".format(type(e).__name__, i),
                                  ProntoWarning)

	def include(self, *terms):
		"""Add new terms to the current ontology.

        Raises:
            TypeError: when the arguments is (are) neither a TermList nor a Term.

        Note:
            This will also recursively include terms in the term's relations
            dictionnary, but it is considered bad practice to do so. If you
            want to create your own ontology, you should only add an ID (such
            as 'ONT:001') to your terms relations, and let the Ontology link
            terms with each other.

        Examples:
            Create a new ontology from scratch

            >>> from pronto import Term, Relationship
            >>> t1 = Term('ONT:001','my 1st term',
            ...           'this is my first term')
            >>> t2 = Term('ONT:002', 'my 2nd term',
            ...           'this is my second term',
            ...           {Relationship('part_of'): ['ONT:001']})
            >>> ont = Ontology()
            >>> ont.include(t1, t2)
            >>>
            >>> 'ONT:002' in ont
            True
            >>> ont['ONT:001'].children
            [<ONT:002: my 2nd term>]

		"""
		ref_needed = False

		for term in terms:
			if isinstance(term, TermList):
				ref_needed = ref_needed or self._include_term_list(term)
			elif isinstance(term, Term):
				ref_needed = ref_needed or self._include_term(term)
			else:
				raise TypeError('include only accepts <Term> or <TermList> as arguments')

		self.adopt()
		self.reference()

	def merge(self, other):
		"""Merge another ontology into the current one.

        Raises:
            TypeError: When argument is not an Ontology object.

        Example:
            >>> from pronto import Ontology
            >>> nmr = Ontology('tests/resources/nmrCV.owl', False)
            >>> po = Ontology('tests/resources/po.obo.gz', False)
            >>> 'NMR:1000271' in nmr
            True
            >>> 'NMR:1000271' in po
            False
            >>> po.merge(nmr)
            >>> 'NMR:1000271' in po
            True

		"""
		if not isinstance(other, Ontology):
			raise TypeError("'merge' requires an Ontology as argument,"
                            " not {}".format(type(other)))

		self.terms.update(other.terms)
		self._empty_cache()
		self.adopt()
		self.reference()

	@staticmethod
	@contextlib.contextmanager
	def _get_handle(path, timeout=2):

		REMOTE = path.startswith(('http', 'ftp'))
		ZIPPED = path.endswith('gz')

		if REMOTE:
			req = six.moves.urllib.request.Request(path, headers={'HTTP_CONNECTION': 'keep-alive'})
			if not ZIPPED or (ZIPPED and six.PY3):
				handle = six.moves.urllib.request.urlopen(req, timeout=timeout)
				if ZIPPED:
					handle = gzip.GzipFile(fileobj=handle)
			else:
				raise io.UnsupportedOperation("Cannot parse a remote zipped file (this is an urllib2 limitation)")

		elif os.path.exists(path):
			handle = gzip.GzipFile(path) if ZIPPED else open(path, 'rb')
		else:
			raise OSError('Ontology file {} could not be found'.format(path))

		try:
			yield handle
		finally:
			handle.close()

	def _include_term_list(self, termlist):
		"""Add terms from a TermList to the ontology.
        """
		ref_needed = False
		for term in termlist:
			ref_needed = ref_needed or self._include_term(term)
		return ref_needed

	def _include_term(self, term):
		"""Add a single term to the current ontology.

        It is needed to dereference any term in the term's relationship
        and then to build the reference again to make sure the other
        terms referenced in the term's relations are the one contained
        in the ontology (to make sure changes to one term in the ontology
        will be applied to every other term related to that term).
        """
		ref_needed = False

		if term.relations:
			for k,v in six.iteritems(term.relations):
				for i,t in enumerate(v):

					#if isinstance(t, Term):
					try:
						if t.id not in self:
							self._include_term(t)
						v[i] = t.id
					except AttributeError:
						pass

					ref_needed = True

		self.terms[term.id] = term
		return ref_needed

	def _empty_cache(self, termlist=None):
		"""Empty the cache associated with each `Term` instance.

        This method is called when merging Ontologies or including
        new terms in the Ontology to make sure the cache of each
        term is cleaned and avoid returning wrong memoized values
        (such as Term.rchildren() TermLists, which get memoized for
        performance concerns)
        """
		if termlist is None:
			for term in six.itervalues(self.terms):
				term._empty_cache()
		else:
			for term in termlist:
				try:
					self.terms[term.id]._empty_cache()
				except AttributeError:
					self.terms[term]._empty_cache()

	@output_str
	def _obo_meta(self):
		"""Generate the obo metadata header and updates metadata.

        When called, this method will create appropriate values for the
        ``auto-generated-by`` and ``date`` fields.

        Note:
            Generated following specs of the unofficial format guide:
            ftp://ftp.geneontology.org/pub/go/www/GO.format.obo-1_4.shtml
        """
		metatags = (
            "format-version", "data-version", "date", "saved-by",
            "auto-generated-by", "import", "subsetdef", "synonymtypedef",
            "default-namespace", "namespace-id-rule", "idspace",
            "treat-xrefs-as-equivalent", "treat-xrefs-as-genus-differentia",
            "treat-xrefs-as-is_a", "remark", "ontology"
        )

		meta = self.meta.copy()
		meta['auto-generated-by'] = ['pronto v{}'.format(__version__)]
		meta['date'] = [datetime.datetime.now().strftime('%d:%m:%Y %H:%M')]

		obo_meta = "\n".join(
            [ # official obo tags
                x.obo if hasattr(x, 'obo') \
                    else "{}: {}".format(k,x)
                        for k in metatags[:-1]
                            for x in meta.get(k, ())
            ] + [ # eventual other metadata added to remarksmock.patch in production code
                "remark: {}: {}".format(k, x)
                    for k,v in sorted(six.iteritems(meta), key=operator.itemgetter(0))
                        for x in v
                            if k not in metatags
            ] + (     ["ontology: {}".format(x) for x in meta["ontology"]]
                            if "ontology" in meta
                 else ["ontology: {}".format(meta["namespace"][0].lower())]
                            if "namespace" in meta
                 else [])
        )

		return obo_meta

	@property
	def json(self):
		"""str: the ontology serialized in json format.
        """
		return json.dumps(self.terms, indent=4, sort_keys=True,
                          default=operator.attrgetter("__deref__"))

	@property
	def obo(self):
		"""str: the ontology serialized in obo format.
        """
		meta = self._obo_meta()
		meta = [meta] if meta else []
		newline = "\n\n" if six.PY3 else "\n\n".encode('utf-8')

		try: # if 'namespace' in self.meta:
			return newline.join( meta + [
                t.obo for t in self
                    if t.id.startswith(self.meta['namespace'][0])
            ])
		except KeyError:
			return newline.join( meta + [
                t.obo for t in self
            ])
