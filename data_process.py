
"""
    Honour Project: ANU Study Planner
    
    Author: Tianshu Wang
    uniID: u6342392
"""

""" 
    Statement: 
        
    This program has been developed on the basis of Lincoln Smith's work.
    It's presented in https://gitlab.anu.edu.au/u5170648/degree-rule-scraper, 
    which is a well-documented degree scraper program by Lincoln. Under
    permission from my supervisor, Sylvie Thiebaux, he shared the access to me
    for the use of data mining in Programs and Courses website during the process
    completing my honour project.
"""

"""
    In this program, we capture data needed from Programs & Courses Website, 
    and reformulate it in the way MiniZinc accepts, in order to build a MiniZinc
    model.
"""

import re
import collections
from datetime import date
from itertools import chain
from math import ceil
from typing import Iterable
try:
    from urllib.parse import ParseResult, urlparse
except:
    from urlparse import ParseResult, urlparse
import numpy as np

import requests
from bs4 import BeautifulSoup
from bs4.element import NavigableString

from requests.exceptions import HTTPError

COURSE_REGEX = r'[A-Z]{4}\d{4}[A-Z]?'
AREA_REGEX = r'[A-Z]{4}'
LEVEL_REGEX = r'\d{4}'
COMPULSORY_REGEX = r'(?<units>\d{1,3}) units from(?: the)? completion of the following (?:compulsory )?course\(?s\)?'
COLLEGE_CODES = {
    'Engineering and Computer Science': ('ENGN', 'COMP')
    }
PLAN_TYPE = {
    'PROGRAM': 'program',
    'MAJOR': 'major',
    'MINOR': 'minor',
    'SPECIALISATION': 'specialisation'
    }
REQUIREMENT_OPERATORS = {
    '==': '==',
    'MAX': '<=',
    'MIN': '>=',
    'AND': 'AND',
    'OR': 'OR',
    }
QUALIFICATION = {
    '==',
    '>=',
    '<=',
    }
ORDER_LABEL = {
    'GLOBAL_BY_LEVEL': 'Global unit values required by level',
    'GLOBAL_BY COLLEGE': 'Global unit values required by College',
    'PRINCIPAL_SINGLE_COURSE': 'Single compulsory course',
    'PRINCIPAL_COMPULSORY_COURSES': 'Set of compulsory courses',
    'PRINCIPAL_MINMAX_MULTIPLE_AREAS': 'Unit value from multiple areas',
    'PRINCIPAL_MINMAX_SINGLE_AREA': 'Unit value from single area',
    'PRINCIPAL_SINGLE_SET': 'Unit value from set of courses',
    'PRINCIPAL_ONE_TIMES_MANY': 'Unit value from single course taken multiple times',
    'PRINCIPAL_SINGLE_SUBPLAN': 'Completion of a sub plan',
    'PRINCIPAL_SUBPLAN_CHOICE': 'Completion of a sub plan chosen from a set of alternatives',
    'UGRAD_SPECIALISATION_COREQ': 'Major required by specialisation',
    'UGRAD_SPECIALISATION_COREQ_CHOICE': 'Major chosen from alternatives required by '
                                         'specialisation',
    'PRINCIPAL_ALTERNATIVE_SETS': 'Select from alternative sets of requirements',
    'ELECTIVES': 'Electives only restricted by global requirements',
    'PROGRESSION': 'Progression depends on requirement text',
    'UNKNOWN_REQUIREMENT': 'Unknown requirement text'
    }
prereq = dict()
coreq = dict()
incompat = dict()

# This array is obtained by the scraper.
COURSE_CODES = {'COMP8173', 'ENGN1217', 'COMP7240', 'COMP1140', 'COMP6262', 'ENGN4511',
                'COMP3310', 'VCPG6001', 'COMP6250', 'ENGN2228', 'ENGN3810',
                'COMP3620', 'ENGN2707', 'ENGN2222', 'ENGN3013', 'COMP4450', 'ENGN3224',
                'COMP1030', 'COMP8460', 'VCPG6100', 'COMP7310', 'COMP6461', 'ENGN2229',
                'ENGN2218', 'COMP2560', 'VCUG3001', 'ENGN6213', 'COMP5923', 'ENGN8833',
                'ENGN6536', 'ENGN8120', 'VCUG3100', 'ENGN6613', 'ENGN3230', 'ENGN3410',
                'COMP4560', 'COMP3650', 'COMP1600', 'ENGN3331', 'COMP1720', 'ENGN2225',
                'COMP6340', 'ENGN3200', 'ENGN8180', 'ENGN6511', 'COMP3320', 'COMP8830',
                'VCUG2004', 'ENGN6524', 'ENGN3334', 'ENGN6615', 'COMP4630', 'COMP8691',
                'ENGN4420', 'COMP3701', 'COMP8300', 'ENGN6520', 'ENGN6420', 'COMP2310',
                'COMP6120', 'COMP4680', 'COMP6361', 'ENGN4536', 'COMP8755', 'ENGN4820',
                'ENGN6528', 'COMP6301', 'ENGN1211', 'ENGN6212', 'COMP3610', 'COMP4330',
                'COMP2410', 'COMP6710', 'COMP3900', 'COMP6331', 'COMP3430', 'ENGN3226',
                'COMP3550', 'ENGN4523', 'COMP8330', 'COMP8670', 'COMP2120', 'ENGN6334',
                'ENGN8100', 'COMP8440', 'COMP6420', 'VCUG2003', 'COMP3100', 'COMP6442',
                'VCUG3200', 'COMP7230', 'COMP8410', 'ENGN6410', 'COMP2550', 'VCPG8001',
                'COMP6330', 'COMP3300', 'ENGN4221', 'COMP8650', 'COMP2130', 'COMP2610',
                'ENGN3820', 'INFT4005F', 'COMP8600', 'ENGN8602', 'COMP4650', 'ENGN6525',
                'COMP8800', 'COMP6730', 'ENGN8537', 'ENGN6250', 'ENGN6224', 'ENGN6331',
                'COMP4130', 'COMP8320', 'COMP3425', 'COMP6719', 'ENGN4625', 'ENGN4525',
                'COMP6466', 'ENGN2226', 'ENGN6601', 'COMP4800', 'COMP8701', 'ENGN8104',
                'COMP6390', 'ENGN6537', 'COMP4670', 'ENGN4810', 'COMP3630', 'COMP2420',
                'ENGN4521', 'ENGN5923', 'ENGN8601', 'ENGN4520', 'ENGN6626', 'ENGN8536',
                'COMP3710', 'COMP3702', 'COMP8100', 'ENGN4513', 'COMP8180', 'COMP8715',
                'COMP4500', 'COMP3500', 'COMP6310', 'ENGN3512', 'COMP8620', 'ENGN6223',
                'COMP1100', 'ENGN4615', 'ENGN3221', 'ENGN6627', 'ENGN4613', 'COMP1710',
                'COMP4660', 'COMP6240', 'VCPG6004', 'COMP6353', 'COMP6490', 'COMP4610',
                'ENGN8831', 'ENGN6516', 'COMP3120', 'COMP3820', 'COMP6311', 'COMP4540',
                'ENGN5920', 'ENGN8820', 'COMP1130', 'INFT4005P', 'COMP6720', 'COMP4005P',
                'ENGN4528', 'COMP6780', 'COMP5920', 'ENGN4522', 'COMP6260',
                'COMP8260', 'ENGN4627', 'VCUG2001', 'COMP2700', 'ENGN4718', 'COMP6670',
                'ENGN8534', 'COMP3530', 'COMP1110', 'ENGN4516', 'COMP4620', 'ENGN4200',
                'COMP6320', 'COMP6300', 'ENGN2706', 'ENGN3223', 'ENGN6512',
                'COMP8820', 'ENGN3712', 'ENGN8637', 'COMP4340', 'VCUG1001', 'COMP3560',
                'COMP3600', 'COMP1040', 'ENGN8830', 'VCUG3002', 'COMP6445', 'ENGN8527',
                'COMP8501', 'COMP6363', 'COMP4005F', 'ENGN4027', 'COMP4006', 'ENGN8224',
                'ENGN4524', 'COMP1730', 'COMP7500', 'COMP6700', 'COMP2140', 'COMP8430',
                'COMP6464', 'COMP6365', 'COMP8190', 'COMP2710', 'COMP3770', 'MATH6005',
                'COMP2300', 'VCPG6002', 'COMP4300', 'VCPG8002', 'ENGN3100', 'ENGN3601',
                'ENGN1218', 'ENGN2219', 'ENGN8170', 'ENGN6625', 'COMP2100', 'ENGN3213',
                'COMP6261', 'ENGN4706', 'COMP8110', 'ENGN2217', 'COMP6470', 'COMP8420',
                'COMP3740', 'COMP2400', 'ENGN3706', 'ENGN4712', 'COMP2620', 'ENGN8538',
                'ENGN8832', 'VCPG6200', 'ENGN6521', 'COMP4600', 'ENGN3212', 'ENGN1215',
                'ENGN8535', 'COMP8502', 'COMP4550', 'ENGN8260', 'COMP8705', 'ENGN4537'
                }

# This array is obtained by the scraper.
AVAILABLE_CODE = {'COMP8180', 'COMP8300', 'COMP6240', 'COMP6250', 'COMP7500', 'COMP8800',
                  'ENGN6250', 'ENGN8830', 'COMP6464', 'ENGN8535', 'COMP6353', 'COMP8502', 
                  'COMP6461', 'ENGN6511', 'ENGN6516', 'ENGN6213', 'ENGN6212', 'COMP8430',
                  'COMP6365', 'COMP8330', 'ENGN8602', 'ENGN6520', 'COMP6120', 'COMP6445',
                  'ENGN6410', 'ENGN8538', 'COMP6470', 'ENGN6627', 'VCPG6004', 'ENGN6626',
                  'ENGN6334', 'COMP6260', 'COMP6310', 'COMP6710', 'COMP6466', 'COMP6442',
                  'COMP6361', 'ENGN6536', 'ENGN8820', 'ENGN8831', 'ENGN8120', 'VCPG6002',
                  'COMP6301', 'ENGN6625', 'ENGN8180', 'COMP6262', 'COMP7230', 'COMP8460',
                  'COMP8320', 'COMP8701', 'COMP8260', 'ENGN8260', 'ENGN6224', 'ENGN6524',
                  'COMP7310', 'COMP6780', 'COMP8650', 'COMP6320', 'COMP8100', 'ENGN8637', 
                  'COMP8110', 'COMP6700', 'COMP8670', 'COMP6720', 'COMP6390',
                  'ENGN8536', 'COMP8755', 'VCPG8001', 'COMP6490', 'ENGN6528', 'MATH6005',
                  'COMP8820', 'COMP8440', 'ENGN8833', 'ENGN8104', 'COMP6311', 'COMP8190', 
                  'COMP6300', 'ENGN6613', 'COMP6420', 'ENGN6521', 'COMP8830', 'COMP6670',
                  'ENGN8537', 'COMP6719', 'ENGN6537', 'ENGN8224', 'COMP8705', 'ENGN6331', 
                  'VCPG6200', 'ENGN6512', 'ENGN8601', 'COMP8600', 'ENGN8527', 'COMP8691',
                  'COMP8715', 'COMP8173', 'ENGN6420', 'COMP8410', 'ENGN6223',
                  'COMP7240', 'COMP8620', 'ENGN8170', 'ENGN6615', 'COMP6331', 'VCPG6001',
                  'COMP6363', 'COMP6330', 'COMP8420', 'COMP8501', 'COMP6261', 'ENGN8534',
                  'ENGN8832', 'ENGN6525', 'COMP6730', 'VCPG8002', 'ENGN8100', 'ENGN6601', 
                  'VCPG6100', 'COMP6340'}

# This array is obtained by the scraper.
UNIT_TIME_SET = {'COMP8620': [1], 'VCPG6004': [1], 'COMP6720': [1], 'COMP8701': [1], 
                 'COMP8460': [1], 'COMP8600': [1], 'VCPG8002': [1], 'ENGN6511': [1], 
                 'COMP6470': [1], 'ENGN8832': [1], 'ENGN6212': [1], 'COMP6353': [1], 
                 'COMP8670': [1], 'COMP6340': [1], 'ENGN6512': [1], 
                 'COMP6461': [1], 'ENGN8104': [2], 'COMP6780': [1], 'ENGN8602': [2, 1], 
                 'COMP6490': [1], 'ENGN8535': [1], 'COMP8502': [1], 'ENGN8170': [2], 
                 'VCPG8001': [1], 'ENGN6625': [1], 'COMP8705': [1], 'COMP6120': [1], 
                 'COMP6320': [1], 'ENGN8831': [1], 'ENGN6524': [1], 'ENGN6615': [1], 
                 'ENGN6525': [1], 'ENGN6223': [1], 'COMP6363': [1], 
                 'COMP6670': [1], 'COMP6311': [1], 'COMP7500': [1], 'COMP8330': [1], 
                 'COMP6250': [1], 'COMP6700': [1], 'ENGN8100': [1], 'COMP8820': [4, 1], 
                 'COMP8300': [1], 'COMP8430': [1], 'COMP8440': [1], 'COMP6442': [1], 
                 'COMP6310': [1], 'COMP6262': [1], 'ENGN6516': [1], 'COMP8755': [2, 1], 
                 'ENGN6613': [1], 'COMP6719': [1], 'COMP8190': [1], 'COMP7310': [1], 
                 'COMP6420': [1], 'MATH6005': [1], 'ENGN6521': [1], 'VCPG6100': [2, 1], 
                 'ENGN6213': [1], 'ENGN8537': [1], 'COMP7230': [1], 'ENGN6520': [1], 
                 'ENGN8830': [1], 'ENGN8260': [1], 'COMP6464': [1], 'COMP8501': [1], 
                 'ENGN6334': [1], 'COMP8100': [1], 'ENGN8536': [1], 'COMP8800': [2], 
                 'ENGN8833': [1], 'ENGN6626': [1], 'ENGN8637': [1], 'ENGN6224': [1], 
                 'COMP6260': [1], 'ENGN6420': [1], 'COMP6331': [1], 'COMP7240': [1], 
                 'COMP6240': [1], 'COMP6390': [1], 'COMP6261': [1], 'COMP6710': [1], 
                 'COMP8420': [1], 'ENGN8527': [1], 'COMP8715': [2, 1], 'VCPG6200': [2, 1], 
                 'COMP6466': [1], 'ENGN6627': [1], 'COMP6361': [1], 'COMP8110': [1], 
                 'COMP8173': [1], 'ENGN6528': [1], 'COMP6301': [1], 'COMP6330': [1], 
                 'ENGN8820': [4, 1], 'VCPG6002': [1], 'COMP8260': [1], 'ENGN8534': [1], 
                 'ENGN6410': [1], 'COMP6445': [1], 'COMP6300': [1], 'VCPG6001': [1], 
                 'COMP8650': [1], 'ENGN6331': [1], 'COMP8830': [4, 1], 'ENGN8601': [2], 
                 'ENGN6537': [1], 'ENGN6250': [1], 'ENGN8180': [2], 'ENGN6536': [1], 
                 'ENGN6601': [1], 'ENGN8224': [1], 'COMP6730': [1], 'COMP6365': [1], 
                 'COMP8410': [1], 'ENGN8120': [1], 'COMP8320': [1], 'ENGN8538': [1], 
                 'COMP8180': [1], 'COMP8691': [1]}

# This array is obtained by the scraper.
SEMESTER = {'COMP6461': ['odd_second', 'even_second', 'odd_second'], 'COMP6390': ['odd_second', 'even_second', 'odd_second'],
            'COMP6250': ['odd_first', 'odd_second', 'even_first', 'even_second', 'odd_first', 'odd_second'],
            'COMP6365': ['even_first', 'even_second', 'odd_first', 'odd_second'],
            'ENGN6213': ['odd_first', 'even_first', 'odd_first'], 'COMP6260': ['odd_second', 'even_second', 'odd_second'],
            'COMP8300': ['even_first', 'even_second', 'odd_first', 'odd_second'],
            'COMP8320': ['even_first', 'even_second', 'odd_first', 'odd_second'], 
            'VCPG8001': ['even_first', 'even_second', 'odd_first', 'odd_second'], 
            'ENGN8224': ['odd_second', 'even_second', 'odd_second'], 
            'ENGN8260': ['odd_first', 'odd_second', 'even_first', 'even_second', 'odd_first', 'odd_second'], 
            'VCPG6001': ['odd_first', 'even_first', 'odd_first'], 'ENGN6626': ['odd_first', 'even_first', 'odd_first'], 
            'COMP6331': ['odd_first', 'even_first', 'odd_first'], 'COMP6310': ['odd_second', 'even_second', 'odd_second'], 
            'COMP8190': ['even_second', 'odd_second'], 'COMP8502': ['even_first', 'even_second', 'odd_first', 'odd_second'], 
            'COMP7500': ['even_first', 'even_second', 'odd_first', 'odd_second'], 
            'ENGN6521': ['odd_first', 'odd_second', 'even_first', 'even_second', 'odd_first', 'odd_second'], 
            'VCPG6200': ['even_first', 'even_second', 'odd_first', 'odd_second'], 
            'COMP8701': ['even_first', 'even_second', 'odd_first', 'odd_second'], 
            'COMP6320': ['odd_first', 'even_first', 'odd_first'], 'COMP6719': ['odd_first', 'even_first', 'odd_first'], 
            'ENGN6511': ['odd_second', 'even_second', 'odd_second'], 'COMP8650': ['odd_first', 'even_first', 'odd_first'], 
            'COMP8800': ['odd_first', 'odd_second', 'even_first', 'even_second', 'odd_first', 'odd_second'], 
            'ENGN6331': ['odd_first', 'even_first', 'odd_first'], 'COMP8180': [], 
            'COMP6363': ['even_first', 'even_second', 'odd_first', 'odd_second'], 'COMP6353': ['odd_second', 'even_first', 'odd_first'], 
            'COMP8820': ['odd_first', 'odd_second', 'even_first', 'even_second', 'odd_first', 'odd_second'], 'COMP8440': [], 
            'COMP6490': ['odd_second', 'even_second', 'odd_second'], 'ENGN8535': ['odd_first', 'even_first', 'odd_first'], 
            'ENGN8830': ['odd_second'], 'COMP6730': ['odd_first', 'odd_second', 'even_second', 'odd_second'], 
            'ENGN6420': ['even_first', 'even_second', 'odd_first', 'odd_second'], 'COMP8173': [], 
            'COMP6311': ['even_first', 'even_second', 'odd_first', 'odd_second'], 'COMP6720': ['odd_second', 'even_second', 'odd_second'], 
            'COMP8420': ['odd_first'], 'ENGN6516': ['odd_second', 'even_second', 'odd_second'], 
            'COMP8260': ['odd_first', 'odd_second', 'even_first', 'even_second', 'odd_first', 'odd_second'], 
            'ENGN8833': ['odd_first'], 'COMP8691': ['odd_second'], 'ENGN6224': ['odd_first', 'even_first', 'odd_first'], 
            'ENGN6525': ['odd_second', 'even_second', 'odd_second'], 'VCPG8002': ['even_first', 'even_second', 'odd_first', 'odd_second'],
            'ENGN8527': ['even_first', 'odd_first'], 'COMP8410': ['odd_first'], 'ENGN6524': ['odd_first', 'even_first', 'odd_first'], 
            'ENGN8637': ['odd_first', 'even_first', 'odd_first'], 'COMP6780': ['odd_first', 'even_first', 'odd_first'], 
            'COMP6442': ['odd_first', 'odd_second', 'even_first', 'even_second', 'odd_first', 'odd_second'], 
            'ENGN6537': ['odd_first', 'even_first', 'odd_first'], 'ENGN6223': ['odd_second', 'even_second', 'odd_second'], 
            'ENGN8602': ['odd_first', 'odd_second', 'even_first', 'even_second', 'odd_first', 'odd_second'], 
            'COMP6120': ['odd_second', 'even_second', 'odd_second'], 'COMP8830': ['odd_first', 'odd_second'], 
            'COMP6420': ['odd_first', 'even_first', 'odd_first'], 'ENGN6410': ['odd_second', 'even_second', 'odd_second'], 
            'ENGN8832': ['odd_second'], 'COMP6670': ['odd_second'], 'ENGN8100': ['odd_first', 'even_first', 'odd_first'], 
            'ENGN8831': ['odd_first'], 'ENGN6212': ['even_first', 'odd_first'], 'COMP8670': ['odd_second', 'even_second', 'odd_second'], 
            'ENGN8534': ['odd_second', 'even_second', 'odd_second'], 'COMP6361': ['odd_second', 'even_second', 'odd_second'],
            'ENGN8170': ['odd_first', 'odd_second', 'even_first', 'even_second', 'odd_first', 'odd_second'], 
            'COMP8755': ['odd_first', 'odd_second', 'even_first', 'even_second', 'odd_first', 'odd_second'], 
            'COMP6330': ['even_second', 'odd_second'], 'COMP8620': ['odd_second'], 
            'COMP6700': ['even_first', 'even_second', 'odd_first', 'odd_second'], 'MATH6005': ['odd_first', 'even_first', 'odd_first'], 
            'ENGN6627': ['odd_second', 'even_second', 'odd_second'], 'ENGN6601': ['odd_first', 'even_first', 'odd_first'], 
            'COMP8330': ['odd_second'], 'COMP6445': ['odd_first', 'even_first', 'odd_first'], 
            'ENGN8104': ['even_first', 'even_second', 'odd_first', 'odd_second'], 'ENGN8537': ['odd_second', 'even_second', 'odd_second'], 
            'COMP6240': ['odd_second', 'even_second', 'odd_second'], 'COMP8705': ['even_first', 'even_second', 'odd_first', 'odd_second'], 
            'VCPG6100': ['even_first', 'even_second', 'odd_first', 'odd_second'], 'COMP6262': ['odd_first', 'even_first', 'odd_first'], 
            'COMP6340': ['odd_first', 'even_first', 'odd_first'], 'COMP6464': ['even_first', 'odd_first'], 'ENGN8120': ['odd_second', 'even_second', 'odd_second'], 
            'COMP8715': ['odd_first', 'odd_second', 'even_first', 'even_second', 'odd_first', 'odd_second'], 'ENGN8538': ['odd_first', 'even_first', 'odd_first'], 
            'COMP6466': ['odd_second', 'even_second', 'odd_second'], 'ENGN8820': ['even_first', 'even_second', 'odd_first', 'odd_second'], 
            'VCPG6004': ['even_first', 'even_second', 'odd_first', 'odd_second'], 'COMP6261': ['odd_second', 'even_second', 'odd_second'], 
            'COMP8501': ['even_first', 'even_second', 'odd_first', 'odd_second'], 'ENGN6528': ['odd_first', 'even_first', 'odd_first'], 
            'COMP8600': ['odd_first', 'even_first', 'odd_first'], 'ENGN6625': ['odd_second', 'even_second', 'odd_second'], 
            'ENGN6250': ['odd_first', 'odd_second', 'even_first', 'even_second', 'odd_first', 'odd_second'], 
            'COMP6470': ['odd_first', 'odd_second', 'even_first', 'even_second', 'odd_first', 'odd_second'], 
            'ENGN6613': ['odd_second', 'even_second', 'odd_second'], 'ENGN6615': ['odd_second', 'even_second', 'odd_second'], 
            'VCPG6002': ['even_second', 'odd_second'], 'ENGN8601': ['even_first', 'even_second', 'odd_first', 'odd_second'], 
            'ENGN8180': ['even_first', 'even_second', 'odd_first', 'odd_second'], 'COMP8110': ['odd_first', 'even_first', 'odd_first'], 
            'ENGN6536': ['odd_second', 'even_second', 'odd_second'], 'COMP6300': ['odd_first', 'even_first', 'odd_first'], 
            'ENGN6520': ['odd_first', 'odd_second', 'even_first', 'even_second', 'odd_first', 'odd_second'], 
            'ENGN6512': ['odd_first', 'even_first', 'odd_first'], 'COMP7240': [], 'ENGN6334': ['odd_second', 'even_second', 'odd_second'], 
            'COMP8460': ['even_first', 'odd_first'], 'ENGN8536': ['odd_second', 'even_second', 'odd_second'], 
            'COMP6710': ['odd_first', 'odd_second', 'even_first', 'even_second', 'odd_first', 'odd_second'], 'COMP7230': [], 
            'COMP8430': ['odd_second'], 'COMP7310': ['even_first', 'even_second', 'odd_first', 'odd_second'], 'COMP8100': ['odd_first'], 
            'COMP6301': ['even_first', 'even_second', 'odd_first', 'odd_second']}

# These arrays were manually recorded by myself.
for c in AVAILABLE_CODE:
    prereq[c] = np.array([[None, None, None],
                          [None, None, None],
                          [None, None, None]])
    coreq[c] = np.array([[None]])
    incompat[c] = np.array([[None, None, None]])

#'COMP8180', 'COMP8300', 'COMP6240', 'COMP6250', 'COMP7500', 'COMP8800',
incompat['COMP8300'] = np.array([['COMP4300', None, None]])
incompat['COMP6240'] = np.array([['COMP2400', 'COMP7240', None]])
prereq['COMP7500'] = np.array([['COMP6301', None, None], ['COMP6340', None, None], ['COMP6420', None, None]])
prereq['COMP8800'] = np.array([['COMP6442', None, None], ['COMP8260', None, None], ['COMP6445', None, None]])
#'ENGN6250', 'ENGN8830', 'COMP6464', 'ENGN8535', 'COMP6353', 'COMP8502', 
prereq['ENGN8830'] = np.array([['ENGN4524', 'ENGN6524', None], [None, None, None], [None, None, None]])
prereq['COMP6464'] = np.array([['COMP6700', 'COMP6710', None], [None, None, None], [None, None, None]])
incompat['COMP6353'] = np.array([['COMP3530', None, None]])
prereq['COMP8502'] = np.array([['COMP6340', None, None], ['COMP6420', None, None], ['COMP7500', None, None]])
incompat['COMP8502'] = np.array([['COMP3702', None, None]])
#'COMP6461', 'ENGN6511', 'ENGN6516', 'ENGN6213', 'ENGN6212', 'COMP8430',
incompat['COMP6461'] = np.array([['COMP4610', None, None]])
incompat['ENGN6511'] = np.array([['ENGN4511', None, None]])
incompat['ENGN6516'] = np.array([['ENGN4516', None, None]])
incompat['ENGN6213'] = np.array([['ENGN3213', None, None]])
incompat['ENGN6212'] = np.array([['ENGN3212', None, None]])
prereq['COMP8430'] = np.array([['COMP7230', None, None], ['COMP6730', 'COMP6710', None], ['COMP6240', 'COMP6420', 'COMP7240']])
incompat['COMP8430'] = np.array([['COMP3430', None, None]])
#'COMP6365', 'COMP8330', 'ENGN8602', 'ENGN6520', 'COMP6120', 'COMP6445',
incompat['COMP6365'] = np.array([['COMP3650', None, None]])
incompat['COMP8330'] = np.array([['COMP4330', None, None]])
coreq['COMP6120'] = np.array([['COMP6442']])
incompat['COMP6120'] = np.array([['COMP2120', 'COMP2130', 'COMP6311']])
incompat['COMP6445'] = np.array([['COMP4450', None, None]])
#'ENGN6410', 'ENGN8538', 'COMP6470', 'ENGN6627', 'VCPG6004', 'ENGN6626',
incompat['ENGN6410'] = np.array([['ENGN3410', None, None]])
incompat['ENGN6627'] = np.array([['ENGN4627', None, None]])
incompat['VCPG6004'] = np.array([['VCUG2004', None, None]])
incompat['ENGN6626'] = np.array([['ENGN3226', None, None]])
#'ENGN6334', 'COMP6260', 'COMP6310', 'COMP6710', 'COMP6466', 'COMP6442',
incompat['ENGN6334'] = np.array([['ENGN3334', 'PHYS3053', 'PHYS6504']])
incompat['COMP6260'] = np.array([['COMP1600', None, None]])
prereq['COMP6310'] = np.array([['COMP6300', None, None], ['COMP6700', 'COMP6710', None], [None, None, None]])
incompat['COMP6310'] = np.array([['COMP2310', None, None]])
incompat['COMP6710'] = np.array([['COMP6700', 'COMP1110', None]])
incompat['COMP6466'] = np.array([['COMP3600', None, None]])
prereq['COMP6442'] = np.array([['COMP6700', 'COMP6710', None], [None, None, None], [None, None, None]])
coreq['COMP6442'] = np.array([['MATH6005']])
incompat['COMP6442'] = np.array([['COMP2100', None, None]])
#'COMP6361', 'ENGN6536', 'ENGN8820', 'ENGN8831', 'ENGN8120', 'VCPG6002',
incompat['COMP6361'] = np.array([['COMP3610', None, None]])
incompat['ENGN6536'] = np.array([['ENGN4536', None, None]])
incompat['VCPG6002'] = np.array([['VCUG3002', None, None]])
#'COMP6301', 'ENGN8528', 'ENGN6625', 'ENGN8180', 'COMP6262', 'COMP7230', 'COMP8460'
incompat['ENGN6625'] = np.array([['ENGN4625', None, None]])
incompat['COMP7230'] = np.array([['COMP1730', 'COMP6730', 'COMP1040']])
incompat['COMP8460'] = np.array([['COMP4600', None, None]])
#'COMP8320', 'COMP8701', 'COMP8260', 'ENGN8260', 'ENGN6224', 'ENGN6524',
incompat['COMP8320'] = np.array([['COMP4340', None, None]])
prereq['COMP8260'] = np.array([['COMP6250', 'COMP8701', None], [None, None, None], [None, None, None]])
incompat['ENGN6224'] = np.array([['ENGN3224', None, None]])
incompat['ENGN6524'] = np.array([['ENGN4524', None, None]])
#'COMP7310', 'COMP6780', 'COMP8650', 'COMP6320', 'COMP8100', 'ENGN8637',
incompat['COMP6780'] = np.array([['COMP1710', None, None]])
prereq['COMP8650'] = np.array([['COMP8600', None, None], [None, None, None], [None, None, None]])
incompat['COMP8650'] = np.array([['COMP4680', None, None]])
prereq['COMP6320'] = np.array([['COMP6710', None, None], [None, None, None], [None, None, None]])
coreq['COMP6320'] = np.array([['COMP6262']])
incompat['COMP6320'] = np.array([['COMP3620', None, None]])
#'COMP8110', 'COMP6700', 'COMP8823', 'COMP8670', 'COMP6720', 'COMP6390',
prereq['COMP8110'] = np.array([['COMP6700', 'COMP6710', None], [None, None, None], [None, None, None]])
incompat['COMP8110'] = np.array([['COMP3120', None, None]])
incompat['COMP6700'] = np.array([['COMP6710', None, None]])
incompat['COMP6720'] = np.array([['COMP1720', None, None]])
incompat['COMP6390'] = np.array([['COMP3900', None, None]])
#'ENGN8150', 'ENGN8536', 'COMP8755', 'VCPG8001', 'COMP6490', 'ENGN6528',
prereq['COMP8755'] = np.array([['COMP8260', None, None], ['COMP6442', None, None], [None, None, None]])
prereq['VCPG8001'] = np.array([['VCPG6001', None, None], [None, None, None], [None, None, None]])
incompat['COMP6490'] = np.array([['COMP4650', None, None]])
incompat['ENGN6528'] = np.array([['ENGN4528', None, None]])
#'COMP8820', 'COMP8440', 'ENGN8833', 'ENGN8104', 'COMP6311', 'COMP8190',
incompat['COMP6311'] = np.array([['COMP2130', None, None]])
#'COMP6300', 'ENGN6613', 'COMP6420', 'ENGN6521', 'COMP8830', 'COMP6670'
coreq['COMP6300'] = np.array([['COMP6700']])
incompat['ENGN6613'] = np.array([['ENGN4613', None, None]])
prereq['COMP6420'] = np.array([['COMP6710', None, None], [None, None, None], [None, None, None]])
incompat['COMP6420'] = np.array([['COMP2420', None, None]])
incompat['COMP8830'] = np.array([['COMP8715', None, None]])
coreq['COMP6670'] = np.array([['COMP6710']])
incompat['COMP6670'] = np.array([['COMP3670', None, None]])
#'ENGN8537', 'COMP6719', 'ENGN6537', 'ENGN8224', 'COMP8705', 'ENGN6331',
incompat['COMP6719'] = np.array([['ENGN2219', None, None]])
incompat['ENGN6537'] = np.array([['ENGN4537', None, None]])
prereq['ENGN8224'] = np.array([['ENGN3223', 'ENGN6223', None], [None, None, None], [None, None, None]])
#'VCPG6200', 'ENGN6512', 'ENGN8601', 'COMP8600', 'ENGN8527',
incompat['ENGN6512'] = np.array([['ENGN3512', None, None]])
prereq['COMP8600'] = np.array([['COMP6670', None, None], [None, None, None], [None, None, None]])
incompat['COMP8600'] = np.array([['COMP4670', None, None]])
#'COMP8715', 'COMP8173', 'ENGN8823', 'ENGN6420', 'COMP8410', 'ENGN6223',
prereq['COMP8715'] = np.array([['COMP8705', 'COMP8260', None], [None, None, None], [None, None, None]])
coreq['COMP8715'] = np.array([['COMP6442']])
incompat['COMP8715'] = np.array([['COMP8830', None, None]])
incompat['ENGN6420'] = np.array([['ENGN4420', None, None]])
prereq['COMP8410'] = np.array([['COMP7240', 'COMP6240', 'COMP2400'], ['COMP6730', 'COMP7230', 'COMP6710'], [None, None, None]])
incompat['COMP8410'] = np.array([['COMP3420', 'COMP3425', None]])
#'COMP7240', 'COMP8620', 'ENGN8170', 'ENGN6615', 'COMP6331', 'VCPG6001',
incompat['COMP7240'] = np.array([['COMP2400', 'COMP6240', None]])
prereq['COMP8620'] = np.array([['COMP6320', None, None], [None, None, None], [None, None, None]])
prereq['ENGN8170'] = np.array([['ENGN8100', None, None], ['ENGN8160', 'ENGN8260', None], [None, None, None]])
incompat['ENGN6615'] = np.array([['ENGN4615', None, None]])
prereq['COMP6331'] = np.array([['COMP6710', 'COMP6310', 'COMP6442'], [None, None, None], [None, None, None]])
incompat['COMP6331'] = np.array([['COMP3310', None, None]])
incompat['VCPG6001'] = np.array([['VCUG3001', None, None]])
#'COMP6363', 'COMP6330', 'COMP8420', 'COMP8501', 'COMP6261', 'ENGN8534',
incompat['COMP6363'] = np.array([['COMP3630', None, None]])
coreq['COMP6330'] = np.array([['COMP6300']])
incompat['COMP6330'] = np.array([['COMP3300', None, None]])
prereq['COMP8501'] = np.array([['COMP6340', None, None], ['COMP6420', None, None], ['COMP7500', None, None]])
incompat['COMP8501'] = np.array([['COMP3701', None, None]])
incompat['COMP6261'] = np.array([['COMP2610', 'ENGN8534', None]])
incompat['ENGN8534'] = np.array([['COMP2610', 'COMP6261', None]])
#'ENGN8832', 'ENGN6525', 'COMP6730', 'VCPG8002', 'ENGN8100', 'ENGN6601', 
incompat['ENGN6525'] = np.array([['ENGN4525', None, None]])
incompat['COMP6730'] = np.array([['COMP1730', 'COMP7230', 'COMP1040']])
incompat['ENGN6601'] = np.array([['ENGN3601', None, None]])
#'VCPG6100', 'COMP6340'}
prereq['VCPG6100'] = np.array([['VCPG6004', None, None], [None, None, None], [None, None, None]])
incompat['COMP6340'] = np.array([['COMP2410', None, None]])

class ReqNode:
    """
    Represent a paragraph in a set of Program Orders on a Programs and Courses page.

    Store the text of the paragraph, as well as enough information about the position of this
    paragraph in the layout of the orders to give it context

    Program Orders are laid out (mostly) in a tree, with a couple of exceptions. These exceptions
    make it useful to be able to determine a particular tree node's siblings. As a result a node
    maintains links to the sibling to either side of it in the resultant tree structure.
    """
    next_sibling = None
    prev_sibling = None
    last_child = None

    def __init__(self, requirement, parent=None, children=None, margin=None):
        """
        :param requirement: The text or list of strings from the paragraph
        :param parent: Parent ReqNode if we want to set it here
        :param children: ReqNode at the head of a list of children
        :param margin: Value of the left-margin attribute of this paragraph in the HTML
        """
        self.requirement = requirement
        self.parent = parent
        if children and not isinstance(children, ReqNode):
            TypeError('Children parameter, if passed, must be an instance of ReqNode.')
        self.children = children
        if children:
            last_child = children
            while last_child.next_sibling:
                last_child = last_child.next_sibling
            self.last_child = last_child
        self.margin = margin

    def __iter__(self):
        current_sibling = self
        while current_sibling:
            yield current_sibling
            current_sibling = current_sibling.next_sibling

    def __str__(self):
        return self.flatten_requirement_text()

    @property
    def is_leaf(self):
        return self.children is None

    @staticmethod
    def _cut_family_ties(node):
        # If this node has existing relationships make a clean break
        if node.prev_sibling:
            node.prev_sibling.next_sibling = node.next_sibling
        if node.next_sibling:
            node.next_sibling.prev_sibling = node.prev_sibling
        node.parent = None
        node.next_sibling = None
        node.prev_sibling = None

    def append_child(self, new_child):
        """
        Append a new ReqNode to the end of the linked list of children.
        :param new_child: The ReqNode to append to the list
        """
        # Avoid complicated family structures
        self._cut_family_ties(new_child)
        # Append child
        if self.children is None:
            self.children = new_child
        else:
            self.last_child.next_sibling = new_child
            new_child.prev_sibling = self.last_child
        new_child.parent = self
        self.last_child = new_child

    def dump_tree(self):
        """Return a tuple/list representation of the tree under this node"""
        if self.children:
            return self.requirement, self.margin, [node.dump_tree() for node in self.children]
        return self.requirement, self.margin, []

    def flatten_requirement_text(self):
        """
        A ReqNode's requirement should be either a string or a list of strings. Attempt to
        flatten it.

        :return: The flattened string for the ReqNode's requirement
        """
        # If we get a requirement that isn't a string or iterable flail arms wildly
        if isinstance(self.requirement, str):
            return self.requirement
        else:
            return ' '.join(self.requirement)

    def flatten_children_text(self):
        """
        Usually the text detailing specific course codes etc. for a requirement is held in its
        children, either as multiple paragraphs in a single child or one paragraph per child,
        depending on the whim of whoever laid out the html for that particular page. Often we
        don't care about structure and just want it as a single string.

        :return: The flattened string.
        """
        return ' '.join([child.flatten_requirement_text() for child in self.children])

    def get_child_text_as_lines(self):
        """
        If there is more than one child return a list containing each child's text, or if there
        is a single child try to preserve line breaks in its text.

        :return: Iterable of the lines of text
        """
        if not self.children:
            return []
        if self.children.next_sibling:
            return [child.flatten_requirement_text() for child in self.children]
        if isinstance(self.children.requirement, str):
            return self.children.requirement.splitlines()
        return [line for line in self.children.requirement if line]

def _get_tag_indent(tag, current_margin):
    """
    Visual structure is often created by adjusting the left margin of the <p> tags e.g.
    style="margin-left: 40px;", so extract that value to help navigate the page layout

    :param tag: HTML tag to extract alignment from
    :param current_margin: Alignment of previous tag so we can adjust for e.g <table> tags
    :return: The alignment of the tag
    """
    if 'style' in tag.attrs:
        match = re.search(r'(margin|padding)-left:\s?(?P<margin>-?\d{1,3})', tag['style'])
        if match:
            new_margin = int(match.group('margin'))
        else:
            new_margin = current_margin
    elif tag.name == 'table':
        # An alternate page structure sometimes found on subplans uses <p> headings and then
        # lays out requirement contents like course lists using a <table>
        new_margin = current_margin
    else:
        # No style attribute means we're not indented
        new_margin = 0
    return new_margin


def _split_multi_req_paragraph(tag, new_margin):
    """
    Apparently sometimes we just jam a whole bunch of requirements in a single <p> tag
    and use <br> to separate them. Restructure our html by walking the contents of this tag
    and separating its children into new paragraphs at the same indent when we hit a <br>
    tag. Delete the <br> tags as we encounter them.

    :param tag:
    :param new_margin:
    :return: A list of the newly created paragraphs
    """
    def _get_new_p_tag():
        return BeautifulSoup(
                '<p style="margin-left: {}px;"><p>'.format(new_margin),
                'html5lib'
                ).p.extract()

    new_paragraphs = []
    current_paragraph = tag  # type: BeautifulSoup
    br_tag = tag.br  # type: BeautifulSoup
    child = br_tag.next_sibling
    br_tag.decompose()
    new_p_tag = _get_new_p_tag()
    while child:
        next_child = child.next_sibling

        # If this is a <br> tag, if we've created a new paragraph with contents insert it
        # after the current paragraph then delete the <br> tag, so it doesn't mess with
        # stuff later.
        if child.name == 'br':
            # Check stripped_strings so we don't process an effectively empty line caused
            #  by adjacent <br> tags
            if list(new_p_tag.stripped_strings):
                current_paragraph.insert_after(new_p_tag)
                current_paragraph = new_p_tag
                new_paragraphs.append(new_p_tag)
                new_p_tag = _get_new_p_tag()
            child.decompose()
        else:
            new_p_tag.append(child)
        child = next_child

    if list(new_p_tag.stripped_strings):
        current_paragraph.insert_after(new_p_tag)
        new_paragraphs.append(new_p_tag)
    return new_paragraphs


def build_reqnode_tree(study_block, header_id='program-requirements'):
    """
    Construct a tree to replicate the structure of the Program Orders as rendered on P&C.

    There is just enough structure to the orders that we need to know their spatial relationship
    on the P&C page, but the html is constructed using <p> tags with margin shifts...

    Most of the time we don't care about the indents as most statements are just AND'd together
    at the top level. Exceptions are choice statements and capturing e.g. course lists that are
    part of certain requirements.

    :param study_block: The containing <div> for the requirements text.
    :param header_id: The ID of the html tag that is the heading for the actual requirements.
    :return: The root of the ReqNode tree structure representing the layout of the requirements.
    """
    root = ReqNode([''], margin=-1)
    current_parent = root
    tag = study_block.find(id=header_id)
    if tag is None:
        raise ValueError("Couldn't find the requirements header on the page, this isn't going "
                         "to work...")
    tag = tag.next_sibling
    current_margin = 0
    alternative_indent = 0
    principal_indent = 0
    processing_alternative = False
    processing_principal = False

    # Content is arranged between <h2> tags so keep grabbing stuff until we hit the end of
    # the <div> or the next <h2>
    while tag and tag.name != 'h2':
        # Empty tag, spacer, go to top link, skip it all
        if (isinstance(tag, NavigableString)
                or ('class' in tag.attrs and 'back-to-top' in tag['class'])):
            tag = tag.next_sibling
            continue

        new_margin = _get_tag_indent(tag, current_margin)

        # Of course there are different margin increments kicking around so normalise them to
        # something consistent, in this case multiples of 40 which is the biggest increment
        # encountered
        if new_margin > 0:
            new_margin = ceil(new_margin / 40) * 40

        # If we've passed the bottom of a requirement and its e.g. course list unset principal
        # requirement processing state.
        if processing_principal and new_margin <= principal_indent:
            processing_principal = False
            principal_indent = 0

        # If we were processing alternatives check if we've exited that block and unset that state.
        if processing_alternative and (
                new_margin <= alternative_indent
                or not ''.join(tag.stripped_strings)
                ):
            processing_alternative = False
            alternative_indent = 0
            current_parent = root

        # Apparently sometimes we just jam a whole bunch of requirements in a single <p> tag
        # and use <br> to separate them. Restructure our html by walking the contents of this tag
        # and separating its children into new paragraphs at the same indent when we hit a <br>
        # tag. Delete the <br> tags as we encounter them.
        if tag.br:
            new_paragraphs = _split_multi_req_paragraph(tag, new_margin)
            # It's also possible the new paragraphs are actually a list of courses that should be
            # indented underneath their parent requirement so try to detect this and adjust
            # margins accordingly
            new_lines = [' '.join(paragraph.stripped_strings) for paragraph in new_paragraphs]
            if (
                    len(new_paragraphs) > 1
                    and not re.match(COURSE_REGEX, ' '.join(tag.stripped_strings))
                    and all([re.match(COURSE_REGEX, line) for line in new_lines])
                    ):
                for paragraph in new_paragraphs:
                    paragraph['style'] = 'margin-left: {}px;'.format(new_margin + 40)

        requirement_text = ' '.join(tag.stripped_strings)

        # If it's a blank line then that typically indicates the end of a requirement block. Take
        # us back to the top level indent
        if new_margin < 0 or not ''.join(tag.stripped_strings):
            current_parent = root
            new_margin = 0
        # Try matching against different requirement regexes
        elif re.match(
                r'Th(e|is) (.*?) requires( the)? completion of (\d{1,3}) units.*?:?$',
                requirement_text
                ):
            root.append_child(ReqNode(list(tag.stripped_strings), margin=new_margin))
        elif re.match(r'(Either|Or):?$', requirement_text):
            # Adjust where the current parent is and set state that we're in a choice block
            new_node = ReqNode(list(tag.stripped_strings), margin=new_margin)
            root.append_child(new_node)
            current_parent = new_node
            alternative_indent = new_margin
            processing_alternative = True
        elif (
                re.match(r'(A maximum of |A minimum of )?\d{1,3} units', requirement_text)
                or re.match(
                    r'This specialisation must be taken in conjunction with',
                    requirement_text
                    )
                ):
            # Set state that we're processing a principal requirement so we can process any
            # children properly
            processing_principal = True
            principal_indent = new_margin
            new_node = ReqNode(list(tag.stripped_strings), margin=new_margin)
            current_parent.append_child(new_node)
        elif re.match(r'The \d{1,3} units must (consist of|include):$', requirement_text):
            pass
        else:
            new_node = ReqNode(list(tag.stripped_strings), margin=new_margin)
            # Either have course/subplan list for a principal requirement
            if processing_principal and new_margin > principal_indent:
                current_parent.last_child.append_child(new_node)
            # Or something else so we just store it
            else:
                current_parent.append_child(new_node)

        current_margin = new_margin
        tag = tag.next_sibling
    return root


def get_requirements_block(soup):
    """
    Locate the requirements block in the html document.

    :param soup: The BeautifulSoup object to search under
    :return: The containing element for all the requirements text
    """
    study_block = soup.find(id='study')
    if study_block is None:
        raise ValueError("Couldn't find a requirements block on the page, this isn't going to "
                         "work...")
    return study_block


# Basic representation of Course information
class Course:
    """
    Store some basic information about a course so we do do useful stuff with it later...
    """
    def __init__(self, code, unit_value, requisites):
        self.code = code
        self.unit_value = unit_value
        self.requisites = requisites


class CourseFilter:
    """
    Parent class of the various types of course filter.
    """
    def get_courses(self):
        raise NotImplementedError()


class CourseListFilter(CourseFilter):
    """Store an iterable of course codes"""
    def __init__(self, course_codes):
#        super().__init__()
        self.course_codes = course_codes
        # Hack automatic collection of seen course codes
        COURSE_CODES.update(set(course_codes))

    def __repr__(self):
        return str(self.get_courses())

    def get_courses(self):
        """Returns the iterable of course codes stored in this object as a list."""
        if isinstance(self.course_codes, list):
            return self.course_codes
        return list(self.course_codes)


def build_course_regex(area_codes=None, levels=None):
    """
    Construct a regex that will filter desired course codes out of some list of codes.

    :param area_codes: A list of area codes e.g ['COMP']
    :param levels: A list of subject level prefix digits e.g. ['1', '4']
    :return: Regex string
    """
    if area_codes:
#        area_prefix = '{}'.format('|'.join(area_codes))
        area_prefix = area_codes
    else:
        area_prefix = AREA_REGEX

    if levels:
        level_suffix = '{}'.format('|'.join(levels))
        level_suffix = level_suffix + r'\d{3}'
    else:
        level_suffix = LEVEL_REGEX

    return r'{}{}[A-Z]?'.format(area_prefix, level_suffix)


class CourseRegexFilter(CourseFilter):
    """Return a list of courses identified by a regular expression."""
    def __init__(self, course_regex):
#        super().__init__()
        self.course_regex = course_regex

    def __repr__(self):
        return self.course_regex

    def get_courses(self, course_codes=None):
        """
        Filter an iterable of course codes based on this object's course_regex attribute.

        :param course_codes: Optional iterable of course codes. Uses COURSE_CODES if not set.
        :return: List of course codes that match self.course_regex.
        """
        if course_codes is None:
            course_codes = COURSE_CODES
        return [code for code in course_codes if re.match(self.course_regex, code)]


class ProgramOrder:
    """
    Details an individual requirement of a degree or similar degree plan level element.

    See https://policies.anu.edu.au/ppl/document/ANUP_006803 for details of Program orders.

    Program orders are a set of requirements which appear to follow the following recursive format:

    order ::= { requirement } ;
    requirement ::= { alternative } ;
    alternative ::= { requirement } ;

    A set of requirements are joined by a logical AND, alternatives by a logical OR. There is no
    negation at this level. An expanded order thus ends up as nested alternating AND/OR clauses e.g.

    req1 & req2 & (req3 | (req4 & re5 & (req6 | req7)) | req8) & req9

    Each requirement ultimately specifies some unit value that it contributes towards the
    completion of a degree and a set of courses that can be used to acquire those units,
    or some administrative hurdle/requirement. Courses define their own rules in terms of
    pre-requisites, co-requisites and incompatible courses etc. so at the Course level logical
    expressions will get more complex.

    At the moment there are really two types of ProgramOrder:
      * One that stores a specific requirement. These have no children and generally apply a unit
        value requirement to a set of courses via some min|max|equals operator.
      * One that is a container of sorts and groups ProgramOrders joined by an AND/OR operator.
    TODO: Split these up into a parent and subclasses so the role is explicit.

    The resulting representation is a tree starting with a container ProgramOrder, and it will
    have children that may themselves be containers, or could be specific requirement ProgramOrders.
    """
    def __init__(self, code, title, text, unit_value, operator,
                 course_filter=None):
        """
        :param code: The program/plan code this ProgramOrder belongs to.
        :param title: An entry in the PROGRAM_ORDER dict that describes this requirement.
        :param text: The raw text that was process to create this ProgramOrder.
        :param unit_value: Unit value which together with the operator and course_filter
        determines if this requirement is met.
        :param operator: Whether the unit value is and exact/max/min requirement.
        :param course_filter: Optional CourseFilter object that describes courses that can be
        used to fulfill the requirement of this ProgramOrder.
        """
        self.code = code
        self.title = title
        self.text = text
        self.unit_value = unit_value
        self.operator = operator
        self.course_filter = course_filter
        self.children = list()
        self.parent = None

    def __str__(self):
        return '{} {}: {} {} units from courses matching {}'.format(
                self.code,
                self.title,
                self.operator,
                self.unit_value,
                self.course_filter
                )

    def add_child(self, new_order):
        if not isinstance(new_order, ProgramOrder):
            raise ValueError("Can't add a non ProgramOrder as a child: {}".format(new_order))
        new_order.parent = self
        self.children.append(new_order)

    def dump_requirements(self):
        """
        Example method that recurses through the ProgramOrder tree and builds up a string
        describing the program's requirements in a sort-of propositional logic statement format.

        :return nested requirement nodes in a tree.
        """
        if self.children:
            join_string = ' {} '.format(self.operator)
            return ' ( {} ) '.format(
                    join_string.join([order.dump_requirements() for order in self.children])
                    )
        result = str(self.course_filter)
        if '[A-Z]?' in result:
            
            # '[A-Z]?' exists could be 3 possibility - (1)it does not find anything; (2)it finds field code only; 
            # (3)it finds level code only.
            
            # '[A-Z]?' refers to a sign for either an area code or a level code.
            if '[A-Z]?' in result:
                # Capture as an area code if the regex expression can match something
                area = re.findall(AREA_REGEX, str(result))
                if area:
                    return '{}{}units {}\n'.format(self.operator, self.unit_value, area[0])
                # Sign for level constraints.
                elif result.find('}')>0:   
                    return '{}{}units {}000level\n'.format(self.operator, self.unit_value, result[1 + result.find('}')])
        return '{}{}units {}\n'.format(self.operator, self.unit_value, self.course_filter)       
        

    def buildAModel(self, known_preference = {}, start_semester = 1, spec = 0, oldPlan = {}, replaced_course = []):
        """
        We construct and write the model file and data file to minizinc in this function.
        
        :param known_preference: A dict defines how much the user prefer to take the course
        :param start_semester: A string denotes in which year and semester the user starts  
        :param spec: A string denotes the intended specialisation 
        :param oldPlan: A dict that indicates the old plan generated from our planner with undesired courses labeled by -1
        :param replaced_course: A list consist of undesired courses
        """
        
        courses = list()
        content = self.dump_requirements()
        
        # Due to the different layout in the Aritificial Intelligence Specialisation 
        # which cannot be recognized by our scraper, we simply provide the information
        # by hand.
        unidentified = '( >=24units None\n AND ==0units None\n AND ==0units None\n AND ==0units None\n AND ==0units None\n )'
        identified = '( ==24units None\n AND ==24units [\'COMP6262\', \'COMP6320\', \'COMP8620\', \'COMP8691\']\n )'
        content = content.replace(unidentified, identified)

        grad_courses = list()
        undergrad_courses = list()
    
        content = content.split('\n')
        new_content = []
        qual = dict()
        unit_qual =dict()
        levelgroup = dict()
        levelgroup['level8'] = list()

        unit_req = list()
        all_req = ''
        preference = dict()
        DEFAULT_PREFERENCE = 3
        
        general = 'include "general.mzn";\n\n'
        var_init_mzn = ''
        constraints_mzn = ''
        solve_mzn = ''
        dzn = ''
        
        # Extract the content obtained by scraper.
        # Put them in a list if there are real courses instead of course sets.
        # Add a list into the big list by searching matched courses through 
        # available courses.
        list_order = 0
        for i in range(len(content)):
            course_list = re.findall(COURSE_REGEX, str(content[i]))
            area_list = re.findall(AREA_REGEX, str(content[i]))
            if course_list:
                courses.append(course_list)
            elif 'level' in content[i]:
                # A level qualification is a constraint on course level,
                # so items in qualification dict do not show up in course lists.
                level = str(re.findall(r'\d{4}', str(content[i]))[0][0])
                
                for j in QUALIFICATION:
                    if j in content[i]:
                        temp = str(content[i])
                        loc = temp.find(j[-1])
                        # Contents to be extracted are within length of 5.
                        unit = re.findall(r'\d{1,3}', str(temp[loc:loc+5]))
                        unit_qual[list_order] = str(unit[0])
                        break
                qual[list_order] = level
                
                continue
            elif area_list:

                # A area qualification is a constraint on course area ('COMP', 'ECON'),
                # which will be replaced by a list of matched courses.

                courses.append([area_list])
                course_list = str(area_list[0])
            elif 'None' in content[i]:

                # If no courses exist, put a None in the list.

                courses.append([None])
                course_list = None
            else:
                continue
            
            # For each qualification, we extract out the unit (e.g. 6 units, 12 units) 
            # and unit_req (e.g. >=96, ==36).
            for j in QUALIFICATION:
                if j in content[i]:
                    temp = str(content[i])
                    loc = temp.find(j[-1])
                    unit = re.findall(r'\d{1,3}', str(temp[loc:loc+5]))
                    unit_req.append(str(j)+str(unit[0]))
                    break
                
            list_order = list_order + 1
            # Numbering each course list by an ascending order.
            new_content = content[i].replace(str(course_list), str(list_order))
            # Replace words by numbers.
            new_content = new_content.replace(str(unit_req[list_order-1]+'units'), ' ')
            all_req = all_req + new_content
        
        # The last right bracket would be ignored so we add a new one here
        all_req = all_req + ' )'        
    
        # Remove extra space
        sep_req = all_req.split(' ')
        while '' in sep_req:
            sep_req.remove('')
            
        # Record qualification location
        qual_loc = list()
        for i in range(len(courses)):
            if not courses[i][0] and unit_req[i] != '==0':
            # it means that it is not a list of courses but a qualification
                for x in range(len(sep_req)):
                    if not sep_req[x] in {'AND', 'OR', '(', ')', ':'} and int(sep_req[x]) == i + 1:
                        sep_req[x+1] = ':'
                        qual_loc.append(x+1)
                        break
                
        # match the right bracket for the left bracket located at (index(:)-2)
        # -> get the range of the qualification
        bracket_list = list()
        qual_range = dict()
        for i in range(len(qual_loc)):
            bracket_list.append('(')
            pos = qual_loc[i]
            lst_num = 0
            while len(bracket_list) != 0:
                pos = pos + 1
                if sep_req[pos] == ')':
                    bracket_list.pop()
                elif sep_req[pos] == '(':
                    bracket_list.append('(')
                elif (not sep_req[pos] == 'AND') and (not sep_req[pos] == 'OR'):
                    lst_num = sep_req[pos]
            qual_range[int(sep_req[qual_loc[i]-1])] = [int(sep_req[qual_loc[i]+1]), int(lst_num)]
            
        # Sort this array qual_range in an ascending order for the purpose of selecting 
        # it correctly when users click on different specialisations.
        qual_range = collections.OrderedDict(sorted(qual_range.items()))
        
        # Clear all non-requirement nodes out from the requirement list.
        while ':' in sep_req:
            loc = None
            for i in range(len(sep_req)):
                if sep_req[i] == ':':
                    loc = i
                    break
            sep_req[loc] = 'AND'
                
        nodes = list()
        # Collect all course list number into the list - nodes.
        for i in range(len(sep_req)):
            if not sep_req[i] in {'AND', 'OR', '(', ')', ':'} and not int(sep_req[i]) in qual_range:
                nodes.append(sep_req[i])
        
        # minizinc output - constraint that describes nodes in the requirement tree.
        for i in range(len(sep_req)):
            if not sep_req[i] in {'AND', 'OR', '(', ')', ':'}:
                thisNode = ''
                if int(sep_req[i]) in qual_range:
                    flag = 1
                    for j in range(qual_range[int(sep_req[i])][0], qual_range[int(sep_req[i])][1]+1):
                        # Exclude those elements which are not course containers
                        if int(unit_req[j-1][2:]) == 0 or j in qual_range:
                            continue
                        if flag:
                            thisNode = 'unit_sum(list' + str(j) + ')'
                            flag = 0
                        else:
                            thisNode = str(thisNode) + ' + ' + 'unit_sum(list' + str(j) + ')'
                    thisNode = str(thisNode) + ' >= '+ str(int(int(unit_req[int(sep_req[i])-1][2:])/6))
                if int(sep_req[i]) in qual:
                    # Output level criteria in the requirement tree
                    if thisNode:
                        thisNode = thisNode + ' /\ '
                    thisNode = thisNode + 'level_criteria(takes, ('
                    flag = 1
                    for k in range((int(qual_range[int(sep_req[i])][0]) - 1), int(qual_range[int(sep_req[i])][1]) + 1):
                        if k == int(nodes[-1]):
                            break
                        if str(k) in nodes:
                            if flag:
                                thisNode = thisNode + 'array2set(list' + str(k) + ')'
                                flag = 0
                            else:
                                thisNode = thisNode + ' union array2set(list' + str(k) + ')'
                    thisNode = thisNode + '), level8, ' + str(int(int(unit_qual[int(sep_req[i])])/6)) + ')'
                elif int(sep_req[i]) not in qual_range:
                    # Output as requirement node when it is not a qualification
                    symbol = unit_req[int(sep_req[i])-1][:2]
                    unit = int(int(unit_req[int(sep_req[i])-1][2:])/6)
                    if '>' in symbol:
                        symbol = 1
                    elif '<' in symbol:
                        symbol = -1
                    elif '==' in symbol:
                        symbol = 0
                    thisNode = 'requirement_node(takes, list' + str(sep_req[i]) + ', ' + str(symbol) + ', ' + str(unit) + ')'
                sep_req[i] = thisNode
                
        # Translate 'and', 'or' to '/\' and '\/' (and, or in minizinc)
        for i in range(len(sep_req)):
            if sep_req[i] == 'AND':
                sep_req[i] = r'/\\'[:-1]
            elif sep_req[i] == 'OR':
                sep_req[i] = r'\\/'[1:]
        
        count = 0
        extra_requirement = list()
        for q in qual_range:
            temp = ''
            flag = 1
            if count == spec:
                for i in range(qual_range[q][0], qual_range[q][1]+1):
                    if int(unit_req[i-1][2:]) == 0 or i in qual_range:
                        continue
                    if flag:
                        temp = str(temp) + 'unit_sum(list' + str(i) + ')'
                        flag = 0
                    else:
                        temp = str(temp) + ' + ' + 'unit_sum(list' + str(i) + ')'
            
                temp = 'constraint (' + str(temp) + ' >= ' + str(int(int(unit_req[q-1][2:])/6)) + ');\n\n'
            
            count = count + 1
            extra_requirement.append(temp)

        for i in extra_requirement:
            constraints_mzn = str(constraints_mzn) + str(i)

        all_req = 'constraint '
        for i in sep_req:
            all_req = all_req + str(i) + ' '
        constraints_mzn = constraints_mzn + all_req + ';\n\n'
        constraints_mzn = constraints_mzn.replace(str(sep_req[-3] + ' ' + sep_req[-2]),'')
        
        # Seperate courses in list into undergraduate courses and graduate courses.
        courses_inlist = list()
        for li in courses:
            for c in li:
                if c==None:
                    break
                elif not isinstance(c, str):
                    for ins in c:
                        for c1 in AVAILABLE_CODE:
                            res = re.findall(build_course_regex(c[0], None), str(c1))
                            if res != [] and not str(res[0]) in courses_inlist:
                                courses_inlist.append(res[0])
                                grad_courses.append(res[0])
                elif isinstance(c, str):
                    if c not in courses_inlist:
                        courses_inlist.append(c)
                        grad_courses.append(c)
        
        # Include all involved courses(requisite and incompatible) into grad courses
        # and undergrad courses.
        while True:
            # This flag will be set to 1 when there are some new courses added into
            # either grad_courses or undergrad_courses; when there is an iteration
            # where it remains 0, it means there is no courses added, so we end this
            # loop.
            flag = 0
            for c in grad_courses:
                for n1 in range(3):
                    for n2 in range(3):
                        if prereq[c][n1][n2] != None and prereq[c][n1][n2] not in grad_courses and prereq[c][n1][n2] not in undergrad_courses:
                            # prerequisite courses always go to the grad_courses list as we are dealing with a grad degree.
                            grad_courses.append(prereq[c][n1][n2])
                            flag = 1
                        if coreq[c][0][0] != None and coreq[c][0][0] not in grad_courses and coreq[c][0][0] not in undergrad_courses:
                            # corequisite courses belong to grad_courses due to the same reason as prerequisite courses.
                            grad_courses.append(coreq[c][0][0])
                            flag = 1
                for n in range(3):
                    if incompat[c][0][n] != None and incompat[c][0][n] not in grad_courses and incompat[c][0][n] not in undergrad_courses:
                        # incompatible courses are undergrad_courses.
                        undergrad_courses.append(incompat[c][0][n])
                        flag = 1
            if flag == 0:
                break

        # Collect all high-level courses
        for i in grad_courses:
            if re.findall(build_course_regex(None, ['8']), i):
                levelgroup['level8'].append(str(i))
                
        # Enter the array into MiniZincs
        levelmzn = 'array[1..' + str(len(levelgroup['level8'])) + '] of courses: level8;\n\n'
        leveldzn = 'level8 = ['
        for i in levelgroup['level8']:
            leveldzn = leveldzn + str(i)
            if i != levelgroup['level8'][-1]:
                leveldzn = leveldzn + ', '
            else:
                leveldzn = leveldzn + '];'


        # All courses in the list.
        temp_courses = list()
        for i in range(len(courses)):
            if isinstance(courses[i][0], str) and courses[i][0] != None:
                for ii in range(len(courses[i])):
                    temp_courses.append(courses[i][ii])
        
        # Output list into Minizinc.
        if len(replaced_course) != 0:
            var_init_mzn = var_init_mzn + 'array[grad_courses] of -1..4: old_plan;\n\n'

        var_init_mzn = var_init_mzn + 'array[grad_courses] of int: preference;\n\n'
        # If we have some courses to be replaced, we are in the refining phase
        if len(replaced_course) != 0:
            solve_mzn = 'solve minimize sum(c in grad_courses where old_plan[c] > 0)(abs(old_plan[c]-takes[c])) + sum(c in grad_courses where old_plan[c] == -1)(abs(takes[c]));'
        # otherwise we only need to maximize the sum of every preference value for courses in the plan
        else:
            solve_mzn = 'solve maximize sum(c in grad_courses where takes[c] != 0)(preference[c]);'

        # if we are in the phase of refining a plan, the old plan will be a part of output            
        if len(replaced_course) != 0:
            for i in replaced_course:
                oldPlan[i] = -1
            for c in grad_courses:
                if c not in oldPlan:
                    oldPlan[c] = 0
            output_oldplan = self.pass_dict(grad_courses, oldPlan, 'old_plan = [')
            dzn = dzn + output_oldplan + '\n\n'
        
        dzn = dzn + 'start_semester = ' + str(start_semester) + ';\n'
        dzn = dzn + 'no_of_grad_courses = ' + str(len(grad_courses)) + ';\n\n'
        
        for c in grad_courses:
            if c not in known_preference:
                preference[c] = DEFAULT_PREFERENCE
            else:
                preference[c] = int(float(known_preference[c])*5)
        output_preference = self.pass_dict(grad_courses, preference, 'preference = [')
        
        dzn = dzn + output_preference + '\n\n'
        
        # Combine grad courses and undergrad courses as one array
        all_courses = grad_courses.copy()
        all_courses.append('None')
        all_courses = all_courses + undergrad_courses
        
        # Reconstructure into MiniZinc
        enum_courses_output = self.pass_enum_or_array(all_courses, 'enum', None, None, 'courses = {')
        enum_grad_courses_output = self.pass_enum_or_array(grad_courses, 'enum', None, None, 'grad_courses = {')
        enum_undergrad_courses_output = self.pass_enum_or_array(undergrad_courses, 'enum', None, None, 'undergrad_courses = {None, ')
        arrayprereq = self.pass_nparray(grad_courses, 3, 3, prereq, 'prereq = [')
        arraycoreq = self.pass_nparray(grad_courses, 1, 1, coreq, 'corequisite = [')
        arrayincompat = self.pass_nparray(grad_courses, 1, 3, incompat, 'incompat = [')
        timeunitavailable = self.pass_enum_or_array(grad_courses, 'array', UNIT_TIME_SET, 'set', 'time_unit_available = [')
        offered_semester = self.pass_enum_or_array(grad_courses, 'array', SEMESTER, 'set', 'offered_semester = [')
        dzn = dzn + str(enum_courses_output) + '\n\n' + str(enum_grad_courses_output) + '\n\n' + str(enum_undergrad_courses_output) + '\n\n'

        # Construct course array as the sequence in the degree requirement
        for i in range(len(courses)):
            # if it is a list of courses
            if isinstance(courses[i][0], str) and courses[i][0] != None:
                str_list = 'list' + str(i+1) + ' = ['
                list_len = len(courses[i])
                for ii in range(len(courses[i])):
                    if ii == len(courses[i]) - 1:
                        str_list = str_list + courses[i][ii] + '];'
                        break
                    str_list = str_list + courses[i][ii] + ', '
                dzn = dzn + str(str_list) + '\n'
                var_init_mzn = var_init_mzn + str('array[1..' + str(list_len) + '] of courses: list' + str(i+1) + ';\n')
            # if it is a fake list denoted as a area code 
            elif isinstance(courses[i][0], list):
                str_list = 'list' + str(i+1) + ' = ['
                list_len = 0
                for ii in range(len(courses[i])):
                    temp = list()
                    for c1 in AVAILABLE_CODE:
                        res = re.findall(build_course_regex(courses[i][0][ii], None), str(c1))
                        if len(res) !=0 and not res[0] in temp_courses:
                            temp.append(res[0])
                    list_len = len(temp)
                    for ti in range(len(temp)):
                        if ti == len(temp) - 1:
                            str_list = str_list + temp[ti] + '];'
                            break
                        str_list = str_list + temp[ti] + ', '
                dzn = dzn + str(str_list) + '\n'
                var_init_mzn = var_init_mzn + str('array[1..' + str(list_len) + '] of courses: list' + str(i+1) + ';\n')
            
        dzn = dzn + str(leveldzn) + '\n\n'
        dzn = dzn + str(arrayprereq) + '\n\n'
        dzn = dzn + str(arraycoreq) + '\n\n'
        dzn = dzn + str(arrayincompat) + '\n\n'      
        dzn = dzn + str(timeunitavailable) + '\n\n'   
        dzn = dzn + str(offered_semester) + '\n\n'
        
        var_init_mzn = var_init_mzn + '\n\n' + levelmzn
        mzn = str(general) + str(var_init_mzn) + str(constraints_mzn) + str(solve_mzn)
        file_object = open('test1.mzn', 'w')
#        file_object = open('experiments/test.mzn', 'w')
        file_object.write(mzn)
        file_object.close( )
        
        file_object = open('test1.dzn', 'w')
#        file_object = open('experiments/test.dzn', 'w')
        file_object.write(dzn)
        file_object.close()
        
        
    def pass_dict(self, input_list, inputdict, outputstr):
        for i in input_list:
            if i == input_list[-1]:
                outputstr = str(outputstr) + str(inputdict[i]) + '];'
            else:
                outputstr = str(outputstr) + str(inputdict[i]) + ', '
        return outputstr
    
    def pass_enum_or_array(self, input_list, outputtype, inputdict, resulttype, outputstr):
        # if there is no dict passed into here, we simply process data contained in 'input_list'
        if not inputdict:
            for i in input_list:
                if i == input_list[-1]:
                    if outputtype == 'enum':
                        outputstr = str(outputstr) + str(i) + '};'
                        break
                    else:
                        outputstr = str(outputstr) + str(i) + '];'
                        break
                outputstr = str(outputstr) + str(i) + ', '
            return outputstr
        
        for i in input_list:
            # specify the output format for the last element
            if i == input_list[-1]:
                # specify cases for output enumberation type
                if outputtype == 'enum':
                    outputstr = str(outputstr) + str(inputdict[i]) + '};'
                    break
                # not enumeration type, in our problem it is array type.
                else:
                    if resulttype == 'set':
                        if inputdict[i] == []:
                            outputstr = str(outputstr) + '{}];'
                        for dim in range(len(inputdict[i])):
                            if len(inputdict[i]) == 1:
                                outputstr = str(outputstr) + '{' + str(inputdict[i][dim]) + '}];'
                            elif dim == len(inputdict[i]) - 1:
                                outputstr = str(outputstr) + str(inputdict[i][dim]) + '}];'
                            elif dim == 0:
                                outputstr = str(outputstr) + '{' + str(inputdict[i][dim]) + ', '
                            else:
                                outputstr = str(outputstr) + str(inputdict[i][dim]) + ', '
                    else:
                        outputstr = str(outputstr) + str(inputdict[i]) + '];'
                    break
                
            # if not the last element, similarly specify how to output for enumberation and array.
            if resulttype == 'set':
                if inputdict[i] == []:
                    outputstr = str(outputstr) + '{}, '
                for dim in range(len(inputdict[i])):
                    if len(inputdict[i]) == 1:
                        outputstr = str(outputstr) + '{' + str(inputdict[i][dim]) + '}, '
                    elif dim == len(inputdict[i]) - 1:
                        outputstr = str(outputstr) + str(inputdict[i][dim]) + '}, '
                    elif dim == 0:
                        outputstr = str(outputstr) + '{' + str(inputdict[i][dim]) + ', '
                    else:
                        outputstr = str(outputstr) + str(inputdict[i][dim]) + ', '
            else:
                outputstr = str(outputstr) + str(inputdict[i]) + ', '
        return outputstr

    def pass_nparray(self, inputdict, ldim, wdim, inputarray, outputstr):
        for i in inputdict:
            for j in range(ldim):
                for k in range(wdim):
                    if i == inputdict[-1] and j == ldim - 1 and k == wdim - 1:                       
                        outputstr = str(outputstr) + str(inputarray[i][j][k]) + '];'
                        break
                    outputstr = str(outputstr) + str(inputarray[i][j][k]) + ', '
        return outputstr



class DegreeRuleScraper:
    """
    Attempt to scrape ANU Program Orders from a html source and create a representation amenable
    to further manipulation.

    At the moment the main interface to the scraper is the build_program_order_struct() method
    which returns a ProgramOrder object, which is the root of a tree of ProgramOrders.
    """
    def __init__(self, path, header_id='program-requirements', plan_type=None, plan_code=None,
                 path_is_file=False):
        """
        :param path: The path of the html resource for this scraper to process. By default the
        scraper assumes this is a URL and tries to request it. If the URL is invalid it assumes
        it is a file path and tries to read the file. If you want to force treating the path as a
        file set path_if_file True.
        :param plan_type: Whether the plan is a progam|major|minor|specialisation
        :param plan_code: The plan code string e.g. MCOMP, ABCD-MAJ etc.
        :param header_id: HTML id of the tag that is the heading for the actual requirements.
        :param path_is_file: Force the scraper to use the path as a file rather than a URL.
        """
        # Extract the year, plan type and code from the path
        self.path = path
        self.plan_type = plan_type
        self.plan_code = plan_code
        self.header_id = header_id
        self.year = date.today().year
        self.path_is_file = path_is_file

        # Try to get some html...
        if path_is_file:
            with open(path) as source_file:
                html = source_file.read()
        else:
            try:
                html = requests.get(path).text
            # requests module URL format errors are all subclasses of ValueError so catch them
            # here and try to process as a file path. Other exceptions should propagate.
            except ValueError:
                with open(path) as source_file:
                    html = source_file.read()

            # Assuming the path was a URL try to extract some useful info.
            parse_result = urlparse(path)
            matches = re.search(
                    r'/?(?P<year>\d{4})?/(?P<plan_type>[a-z]+)/(?P<plan_code>[A-Z\d-]+)$',
                    parse_result.path
                    )
            if matches:
                self.year = matches.group('year') or self.year
                self.plan_type, self.plan_code = matches.group('plan_type', 'plan_code')

        self.soup = BeautifulSoup(html, 'html5lib')
        self.reqnode_tree = build_reqnode_tree(get_requirements_block(self.soup), self.header_id)

    def __repr__(self):
        return '{}, header_id={}, plan_type={}, plan_code={}, path_is_file={}'.format(
                self.path,
                self.header_id,
                self.plan_type,
                self.plan_code,
                self.path_is_file
                )

    def __str__(self):
        return self.path

    def build_subplan_url(self, subplan_url):
        """
        Build an absolute path for a subplan reference in the requirements of another program/plan.
        :param subplan_url: The relative path extracted from the links on a program/plan page.
        :return: The absolute path for the subplan
        """
        parsed_subplan = urlparse(subplan_url)
        parsed_base = urlparse(self.path)
        return ParseResult(parsed_base.scheme, parsed_base.netloc, parsed_subplan.path,
                           '', '', '').geturl()

    def get_subplan_header_(self, subplan_type):
        """
        Get the subplan header element in the study block.

        :param subplan_type: Subplan type
        :return:
        """
        subplan_type = subplan_type.lower()
        if not subplan_type.endswith('s'):
            subplan_type += 's'
        study_block = get_requirements_block(self.soup)
        return study_block.find('h2', id=subplan_type)

    @staticmethod
    def get_subplan_links(subplan_header):
        """
        Get a dict of <display_text>: <path> entries for the links in a particular subplan block.
        :param subplan_header:
        :return:
        """
        links = {}
        if subplan_header.next_sibling:
            tag = subplan_header.next_sibling
            # Skip over any e.g. newline strings.
            while tag and isinstance(tag, NavigableString):
                tag = tag.next_sibling

            for descendant in tag.descendants:
                if descendant.name == 'a':
                    links[' '.join(descendant.stripped_strings)] = descendant['href']
        return links

    def get_subplan_url(self, subplan_title, subplan_type):
        """
        Get a link to a specific subplan.

        :param subplan_title:
        :param subplan_type:
        :return:
        """
        subplan_links = self.get_subplan_links(self.get_subplan_header_(subplan_type))
        return subplan_links[subplan_title]

    @staticmethod
    def _minmax_operator(re_match):
        """
        Get the operator to apply to this requirement from the re match group.
        :param re_match: A re module match result
        :return: An operator from REQUIREMENT_OPERATORS
        """
        # Catch IndexError exceptions as we don't always match on both min and max.
        try:
            if re_match.group('max'):
                return REQUIREMENT_OPERATORS['MAX']
        except IndexError:
            pass
        try:
            if re_match.group('min'):
                return REQUIREMENT_OPERATORS['MIN']
        except IndexError:
            pass
        return REQUIREMENT_OPERATORS['==']

    @staticmethod
    def _extract_child_text(node):
        """
        For requirements that reference sets of some kind, sometimes these aren't indented
        properly so attempt to extract the appropriate text from children or siblings.

        :param node: The node that should have children, but might not.
        :return: The text we extracted from child nodes, or maybe siblings
        """
        if node.children:
            return node.flatten_children_text()
        # Node should have children but doesn't, process sibling text while it looks like a
        # course or study area in a list
        sibling = node.next_sibling
        sibling_text = sibling and sibling.flatten_requirement_text()
        child_text = []
        while sibling_text and re.match(AREA_REGEX, sibling_text):
            child_text.append(sibling_text)
            sibling = sibling.next_sibling
            sibling_text = sibling and sibling.flatten_requirement_text()
        return ' '.join(child_text)

    def process_global_requirements(self, node):
        """
        Global requirements need a little bit more processing so do that here.

        :param node: Node that matches a global requirement regex
        :return: The requirements for the program/plan
        """
        requirement_text = node.flatten_requirement_text()
        # Get the overall unit value requirements
        matches = re.match(
                r'Th(e|is) (?P<plan_title>.*?) requires( the)? completion of (?P<units>\d{1,'
                r'3}) units(, )?(?P<more_globals>of which)?.*?:?$',
                requirement_text
                )
        if matches:
            title = matches.group('plan_title')
            units = int(matches.group('units'))
        else:
            raise ValueError("Couldn't find a properly formatted global requirements header.")

        operator = REQUIREMENT_OPERATORS['MIN']
        if title in ('major', 'minor', 'specialisation'):
            title = ORDER_LABEL['PRINCIPAL_SINGLE_SUBPLAN']
            operator = REQUIREMENT_OPERATORS['==']

        new_order = ProgramOrder(
                self.plan_code,
                title,
                requirement_text,
                units,
                operator
                )
        yield new_order
        # Process requirements that are the children of a global statement
        if node.children:
            for child_node in node.children:
                for new_order in self.process_requirement_node(child_node):
                    yield new_order

    def process_alternative_sets(self, node):
        """
        Process a requirement node that is represented by alternative sets of principal
        requirements.

        :param node: The requirement node that starts the alternating sets.
        :return: The ProgramOrder containing the sets of alternative requirements.
        """
        alternative_orders = ProgramOrder(
                self.plan_code,
                ORDER_LABEL['PRINCIPAL_ALTERNATIVE_SETS'],
                node.flatten_requirement_text(),
                -1,
                REQUIREMENT_OPERATORS['OR']
                )
        # Construct a list of the start node of each set of alternative requirements.
        alternatives = [node.children]
        sibling = node.next_sibling
        while sibling and re.match(r'Or:?$', sibling.flatten_requirement_text()):
            alternatives.append(sibling.children)
            sibling = sibling.next_sibling
        # Go through the alternatives and process each set of requirements
        for alternative in alternatives:
            alternative_container = ProgramOrder(
                    self.plan_code,
                    ORDER_LABEL['PRINCIPAL_ALTERNATIVE_SETS'],
                    '',
                    -1,
                    REQUIREMENT_OPERATORS['AND']
                    )
            # Add each requirement from the set to its container ProgramOrder
            for principal_req in alternative:
                alternative_container.add_child(
                        self.process_principal_requirement(principal_req)
                        )
            alternative_orders.add_child(alternative_container)
        return [alternative_orders]

    def process_principal_requirement(self, node):
        """
        Process nodes that mostly result in pretty straight forward rules...

        WARNING: Ginormous set of if statements follows

        :param node: ReqNode to process
        :return: Program Orders extracted from this node and its children
        """
        # o_O O_o ... O_O
        principal_req_regex = {
            'single_course': r'(?P<units>\d{1,3}) units from(?: the)? completion of (?P<code>['
                             r'A-Z]{4}\d{4}[A-Z]?)',
            'compulsory_set': r'(?P<units>\d{1,3}) units from(?: the)? completion of the following '
                              r'(?:compulsory )?course\(?s\)?',
            'single_area': r'(?P<min>A minimum of )?(?P<max>A maximum of )?(?P<units>\d{1,'
                           r'3}) units from(?: the)? completion of(?: further)? courses from the '
                           r'subject area (?P<area>[A-Z]{4}) ',
            'multiple_areas': r'(?P<min>A minimum of )?(?P<max>A maximum of )?(?P<units>\d{1,'
                              r'3}) units from(?: the)? completion of courses from the following '
                              r'subject areas',
            'single_set': r'(?P<min>A minimum of )?(?P<max>A maximum of )?(?P<units>\d{1,3}) '
                          r'units(?: may come| must come)? from(?: the)? completion of.*? courses? '
                          r'from the following(?: list)?',
            'single_set2': r'(?P<min>A minimum of )?(?P<max>A maximum of )?(?P<units>\d{1,3}) '
                           r'units(?: may come| must come)? from( one of)?(?: the)? following.*? '
                           r'courses?',
            'single_course_multi': r'(?P<min>A minimum of )?(?P<max>A maximum of )?(?P<units>\d{1,'
                                   r'3}) units from(?: the)? completion of (?P<code>[A-Z]{4}\d{4}['
                                   r'A-Z]?).*?, which (?:may|must) be completed more than once('
                                   r'?P<topic>, in a different topic in each instance)?('
                                   r'?P<consecutive>, in consecutive semesters)?',
            'single_subplan': r'\d{1,3} units from(?: the)? completion of the (?P<title>.*?) '
                              r'(?P<subplan>major|minor|specialisation)',
            'subplan_choice': r'\d{1,3} units from(?: the)? completion of one of the following '
                              r'(?:.*?)(?P<subplan>majors|minors|specialisations)',
            'specialisation_coreq': r'This specialisation must be taken in conjunction with the ('
                                    r'?P<title>.*?) major',
            'specialisation_coreq_choice': r'This specialisation must be taken in conjunction with '
                                           r'a major from the following list',
            'electives': r'(?P<units>\d{1,3}) units from(?: the)? completion of elective courses '
                         r'offered by ANU',
            'global_level': r'(?P<min>A minimum of )?(?P<max>A maximum of )?(?P<units>\d{1,3}) '
                            r'units(?: (may|must|that) come)? from(?: the)?(?: completion of)?(?: '
                            r'further)? (?P<level>\d)0{3}-(?:level)?.*? courses(?P<subject_area> '
                            r'from the subject area [A-Z]{4}.*)?',
            'global_college': r'A minimum of (?P<units>\d{1,3}) units must come from completion '
                              r'of courses offered by the ANU College of (?P<college>[A-Z].*?)\.?$',
            'progression': r'(Students must achieve|Students who do not achieve)',
            'TEMPLATE': r'(?P<min>A minimum of )?(?P<max>A maximum of )?(?P<units>\d{1,3}) units '
                        r'from(?: the)? completion of courses from...',
            }
        requirement_text = node.flatten_requirement_text()

        # Single course taken multiple times. This has to be tested before a the single
        # compulsory course regex as they overlap enough that creating sufficiently discerning
        # regexes is fiddly.
        matches = re.match(principal_req_regex['single_course_multi'], requirement_text)
        if matches:
            operator = self._minmax_operator(matches)
            new_order = ProgramOrder(
                    self.plan_code,
                    ORDER_LABEL['PRINCIPAL_ONE_TIMES_MANY'],
                    requirement_text,
                    int(matches.group('units')),
                    operator,
                    CourseListFilter([matches.group('code')])
                    )
            return new_order

        # Single compulsory course
        matches = re.match(principal_req_regex['single_course'], requirement_text)
        if matches:
            new_order = ProgramOrder(
                    self.plan_code,
                    ORDER_LABEL['PRINCIPAL_SINGLE_COURSE'],
                    requirement_text,
                    int(matches.group('units')),
                    REQUIREMENT_OPERATORS['=='],
                    CourseListFilter([matches.group('code')])
                    )
            return new_order

        # Set of compulsory courses
        matches = re.match(principal_req_regex['compulsory_set'], requirement_text)
        if matches:
            child_text = self._extract_child_text(node)
            new_order = ProgramOrder(
                    self.plan_code,
                    ORDER_LABEL['PRINCIPAL_COMPULSORY_COURSES'],
                    ' '.join([requirement_text, child_text]),
                    int(matches.group('units')),
                    REQUIREMENT_OPERATORS['=='],
                    CourseListFilter(re.findall(COURSE_REGEX, child_text))
                    )
            return new_order

        # Single study area
        matches = re.match(principal_req_regex['single_area'], requirement_text)
        if matches:
            operator = self._minmax_operator(matches)
            new_order = ProgramOrder(
                    self.plan_code,
                    ORDER_LABEL['PRINCIPAL_MINMAX_SINGLE_AREA'],
                    requirement_text,
                    int(matches.group('units')),
                    operator,
                    CourseRegexFilter(build_course_regex(area_codes=[matches.group('area')]))
                    )
            return new_order

        # Multiple study areas
        matches = re.match(principal_req_regex['multiple_areas'], requirement_text)
        if matches:
            operator = self._minmax_operator(matches)
            child_text = self._extract_child_text(node)
            new_order = ProgramOrder(
                    self.plan_code,
                    ORDER_LABEL['PRINCIPAL_MINMAX_MULTIPLE_AREAS'],
                    ' '.join([requirement_text, child_text]),
                    int(matches.group('units')),
                    operator,
                    CourseRegexFilter(
                            build_course_regex(area_codes=re.findall(AREA_REGEX, child_text))
                            )
                    )
            return new_order

        # Single set of courses. This must come after the "multiple_areas" regex due to
        # potential overlap.
        matches = re.match(principal_req_regex['single_set'], requirement_text)
        if not matches:
            matches = re.match(principal_req_regex['single_set2'], requirement_text)
        if matches:
            operator = self._minmax_operator(matches)
            child_text = self._extract_child_text(node)
            new_order = ProgramOrder(
                    self.plan_code,
                    ORDER_LABEL['PRINCIPAL_SINGLE_SET'],
                    ' '.join([requirement_text, child_text]),
                    int(matches.group('units')),
                    operator,
                    CourseListFilter(re.findall(COURSE_REGEX, child_text))
                    )
            return new_order

        # Single subplan
        matches = re.match(principal_req_regex['single_subplan'], requirement_text)
        if matches:
            # Follow link to subplan and insert requirements for subplan...
            subplan_type = matches.group('subplan')
            subplan_title = matches.group('title')
            subplan_url = self.build_subplan_url(self.get_subplan_url(subplan_title, subplan_type))
            subplan_scraper = DegreeRuleScraper(subplan_url, header_id='requirements')
            return subplan_scraper.build_program_order_struct()

        # Subplan choice
        matches = re.match(principal_req_regex['subplan_choice'], requirement_text)
        if matches:
            # Create a container order, then get each subplan alternative and add its
            # ProgramOrder tree as a child of the container.
            new_order = ProgramOrder(
                    self.plan_code,
                    ORDER_LABEL['PRINCIPAL_SUBPLAN_CHOICE'],
                    node.flatten_requirement_text(),
                    -1,
                    REQUIREMENT_OPERATORS['OR']
                    )
            subplan_type = matches.group('subplan')
            subplan_options = node.get_child_text_as_lines()
            for subplan_title in subplan_options:
                subplan_url = self.build_subplan_url(
                        self.get_subplan_url(subplan_title, subplan_type)
                        )
                subplan_scraper = DegreeRuleScraper(subplan_url, header_id='requirements')
                subplan_orders = subplan_scraper.build_program_order_struct()
                new_order.add_child(subplan_orders)
            return new_order

        # Specialisation co-requisite
        matches = re.match(principal_req_regex['specialisation_coreq'], requirement_text)
        if matches:
            # Follow link to subplan and insert requirements for subplan...
            subplan_type = 'major'
            subplan_title = matches.group('title')
            subplan_url = self.build_subplan_url(self.get_subplan_url(subplan_title, subplan_type))
            subplan_scraper = DegreeRuleScraper(subplan_url, header_id='requirements')
            return subplan_scraper.build_program_order_struct()

        # Specialisation co-requisite from alternatives
        matches = re.match(principal_req_regex['specialisation_coreq_choice'], requirement_text)
        if matches:
            # Create a container order, then get each subplan alternative and add its
            # ProgramOrder tree as a child of the container.
            new_order = ProgramOrder(
                    self.plan_code,
                    ORDER_LABEL['UGRAD_SPECIALISATION_COREQ_CHOICE'],
                    node.flatten_requirement_text(),
                    -1,
                    REQUIREMENT_OPERATORS['OR']
                    )
            subplan_type = 'major'
            subplan_options = node.get_child_text_as_lines()
            for subplan_title in subplan_options:
                subplan_url = self.build_subplan_url(
                        self.get_subplan_url(subplan_title, subplan_type)
                        )
                subplan_scraper = DegreeRuleScraper(subplan_url, header_id='requirements')
                subplan_orders = subplan_scraper.build_program_order_struct()
                new_order.add_child(subplan_orders)
            return new_order

        # Global requirement by course level (and maybe area as well).
        matches = re.match(principal_req_regex['global_level'], requirement_text)
        if matches:
            units = int(matches.group('units'))
            operator = self._minmax_operator(matches)
            # Extract course level and area details from the regex matches
            course_levels = re.findall(r'(\d)000', requirement_text)
            area_codes = None
            if matches.group('subject_area'):
                area_codes = re.findall(r'[A-Z]{4}', matches.group('subject_area'))
            course_filter = CourseRegexFilter(build_course_regex(area_codes, course_levels))
            return ProgramOrder(
                    self.plan_code,
                    ORDER_LABEL['GLOBAL_BY_LEVEL'],
                    requirement_text,
                    units,
                    operator,
                    course_filter
                    )

        # Global requirement by College.
        matches = re.match(principal_req_regex['global_college'], requirement_text)
        if matches:
            units = int(matches.group('units'))
            area_codes = COLLEGE_CODES[matches.group('college')]
            course_filter = CourseRegexFilter(build_course_regex(area_codes))
            return ProgramOrder(
                    self.plan_code,
                    ORDER_LABEL['GLOBAL_BY COLLEGE'],
                    requirement_text,
                    units,
                    REQUIREMENT_OPERATORS['MIN'],
                    course_filter
                    )

        # Electives
        matches = re.match(principal_req_regex['electives'], requirement_text)
        if matches:
            new_order = ProgramOrder(
                    self.plan_code,
                    ORDER_LABEL['ELECTIVES'],
                    requirement_text,
                    int(matches.group('units')),
                    REQUIREMENT_OPERATORS['=='],
                    CourseRegexFilter(r'.*')
                    )
            return new_order

        raise ValueError('Unknown principal requirement: {}'.format(requirement_text))

    def process_requirement_node(self, node):
        """
        Work out what to do with a given node in the requirements tree.

        Basically try a whole bunch regexs and branch depending on what matches.
        :param node: The ReqNode to process
        :return:
        """
        requirement_text = node.flatten_requirement_text()

        # Process globals
        if re.match(
                r'Th(e|is) (.*?) requires( the)? completion of (\d{1,3}) units.*?:?$',
                requirement_text
                ):
            return self.process_global_requirements(node)

        # Process principal requirements that follow additional global requirements
        elif re.match(r'The \d{1,3} units must consist of:$', requirement_text):
            return chain.from_iterable(
                    [self.process_requirement_node(child_node) for child_node in node.children]
                    )

        # Principal requirements, some double counting and split requirements will be caught by this
        elif re.match(
                r'(A maximum of |A minimum of )?\d{1,3} units( (may|must|that) come)? '
                r'from( the)?( completion of)?',
                requirement_text
                ):
            return [self.process_principal_requirement(node)]

        # Progression requirement
        elif re.match(
                r'(Students must achieve|Students who do not achieve)',
                requirement_text
                ):
            new_order = ProgramOrder(
                    self.plan_code,
                    ORDER_LABEL['PROGRESSION'],
                    requirement_text,
                    0,
                    REQUIREMENT_OPERATORS['==']
                    )
            return [new_order]

        # Specialisation corequisites
        elif re.match(r'This specialisation must be taken in conjunction with', requirement_text):
            return [self.process_principal_requirement(node)]

        elif re.match(r'Either:?$', requirement_text):
            return self.process_alternative_sets(node)

        # Or: statements were already processed by the Either: statement
        elif re.match(r'Or:?$', requirement_text):
            return []
        return [
            ProgramOrder(
                    self.plan_code,
                    ORDER_LABEL['UNKNOWN_REQUIREMENT'],
                    requirement_text,
                    0,
                    REQUIREMENT_OPERATORS['==']
                    )
            ]

    def build_program_order_struct(self):
        """
        Process the tree of ReqNodes to extract program orders and create a representation of linked
        ProgramOrders

        :return: Root of a tree of ProgramOrders representing the program/plan.
        """
        if not self.reqnode_tree.children:
            raise ValueError('Tried to build program orders from an empty requirements tree.')

        program_order_root = ProgramOrder(
                self.plan_code,
                '',
                '',
                -1,
                REQUIREMENT_OPERATORS['AND'],
                )
        for node in self.reqnode_tree.children:
            for new_order in self.process_requirement_node(node):
                program_order_root.add_child(new_order)

        return program_order_root

class PandCScraper(object):
    """
    Attempts to extract various bits of information from the Programs and Courses 
    page for a Course for a given year.

    Parameters
    ----------
    code : String
           Course code for the Course we want to scrape.
    year : String/Integer, optional
           Year to scrape details for if we don't want the current P&C default year.
    """
    pandc_default_url = 'http://programsandcourses.anu.edu.au/course/{}/'
    pandc_year_url = 'http://programsandcourses.anu.edu.au/{}/course/{}/'

    def __init__(self, code, year=None):
        self.code = code.upper()

        if year is None:
            self.pandc_url = self.pandc_default_url.format(code.upper())
        else:
            self.pandc_url = self.pandc_year_url.format(year, code.upper())

        response = requests.get(self.pandc_url, timeout=10)
        response.raise_for_status()

        # html5lib parser is slow and isn't built in, but seems to deal with some
        # poorly formatted P&C HTML better (e.g. <br> tags being immediately closed
        # instead of nesting the following content inside it)
        self.soup = BeautifulSoup(response.content, "html5lib")
        if self.soup.find('p', class_='error-page-message'):
            raise HTTPError('The page {} could not be found'.format(self.pandc_url))

        if year is None:
            year = self.get_academic_year()
        self.year = year

        # Get roots of various sections
        self.roots = {
                'introduction': self.soup.find("div", id="introduction"),
                'learning_outcomes': self.get_siblings_after("learning-outcomes"),
                'indicative_assessments': self.get_siblings_after("indicative-assessment"),
                'workload': self.get_siblings_after("workload"),
                'prescribed_texts': self.get_siblings_after("prescribed-texts"),
                'other_information': self.get_siblings_after("other-information"),
                'req_and_incomp': self.get_siblings_after("incompatibility"),
                }

    @staticmethod
    def _fix_whitespace(text):
        """Replace whitespace in a string with single spaces."""
        return ' '.join(text.split())

    def _join_strings(self, strings):
        """Replace whitespace in strings with single spaces, then join with newlines."""
        return "\n".join([self._fix_whitespace(string) for string in strings])

    def get_siblings_after(self, start_id, start_tag='h2', end_tag=None):
        if end_tag is None:
            end_tag = start_tag

        strt = self.soup.find(start_tag, id=start_id)

        if strt is None:
            return None

        out_root = BeautifulSoup("", "html.parser")
        # out_root = out_soup.document

        contents = []
        nxt = strt.next_sibling
        while nxt is not None and nxt.name != end_tag:
            contents.append(nxt)
            nxt = nxt.next_sibling

        for c in contents:
            out_root.append(c)

        return out_root

    def get_summary_detail(self, detail_name):
        """
        Extract the entry identified by `detail_name` from the course summary block. Return a
        list of strings in the detail block, or `None` if no block matching `detail_name` was
        found.
        """
        # Get the div containing the summary details
        block = self.soup.find('div', class_='degree-summary__codes')
        if not block:
            return None

        # Summary details are in a ul, with headings and contents in span elements. Work out which
        # of the li elements is the one we want by matching against the 'heading' span contained
        # within it.
        ul_elements = block.find_all('li', class_='degree-summary__code')
        detail_li = None
        # Take the first list element that matches our detail name
        try:
            detail_li = next((
                    li_element
                    for li_element in ul_elements
                    if detail_name in li_element.find(
                        'span',
                        class_='degree-summary__code-heading')
                    ))
        except StopIteration:
            return None

        return [
                span.get_text(strip=True)
                for span in detail_li.find_all('span', class_='degree-summary__code-text')
                if span.get_text(strip=True)
                ]
        
    def get_time_unit(self):
        block = self.soup.find(id='offerings-and-fees').find('div', class_='body__inner w-doublewide copy').find_all('div', limit=1)[0]
        if not block:
            return None
        
        val = block.find_all('dd', limit=2)[-1].string
        time_unit = list()
        if '24' in val:
            time_unit.append(4)
            if '12' in val:
                time_unit.append(2)
            else:
                time_unit.append(1)
            return time_unit
        elif '12' in val:
            time_unit.append(2)
            if '6' in val:
                time_unit.append(1)
            return time_unit
        time_unit.append(1)
        return time_unit

    def get_offerings_table(self):
        return self.soup  # soup.find("div", id="tabs-container").find("table")

    @staticmethod
    def get_offerings_headings(table):
        # table = get_offerings_table(soup)
        ths = table.find("thead").find("tr").find_all("th")
        return [a.get_text(strip=True) for a in ths]

    @staticmethod
    def get_offerings_contents(table):
        # table = get_offerings_table(soup)
        trs = table.find("tbody").find_all("tr")[1:]
        return [
                [td.get_text(strip=True) for td in tr.find_all("td")]
                for tr in trs
                ]

    def get_offerings_dict(self, soup):
        headings = self.get_offerings_headings(soup)
        contents = self.get_offerings_contents(soup)
        offerings = []
        for row in contents:
            if len(row) > 1:
                # offerings rows can (very occasionally) consist of only a text heading
                # (see ENGN4520). Exclude these rows.
                offerings.append(dict(zip(headings, row)))
        return offerings

    def get_offerings_detail(self, soup, detail_string):
        offerings = self.get_offerings_dict(soup)
        return [a[detail_string] for a in offerings]

    def get_offerings_all(self):
        root = self.soup.find("div", id="tabs-container")
        if root is None:
            return root
        years = {}
        for i in range(1, 4):
            id = "course-tab-{}".format(i)
            yearname_el = root.find("a", href="#"+id)
            if yearname_el is not None:
                    yearname = yearname_el.text
                    yeartab = root.find("div", id=id)
                    year_offerings = {}
                    for el_semname in yeartab.find_all("h3"):
                        semname = el_semname.text
                        tbl = el_semname.find_next_sibling("")
                        offerings = self.get_offerings_dict(tbl)
                        year_offerings[semname] = offerings
                    years[yearname] = year_offerings
        return years

    # extract specific parts of course details
    def get_academic_year(self):
        """Extract the acadmic year from the page we're processing."""
        return self.soup.find('a', class_='current-academic-year__toggle').get_text(strip=True)

    def get_available_years(self):
        """Extract the list of academix years available on P&C."""
        soup = self.soup.find('div', class_='intro__apply-to-study__current-academic-year')
        return list(soup.find('ul').stripped_strings)

    def get_title(self):
        return self.soup.find("h1", class_="intro__degree-title").get_text(strip=True)

    def get_introduction(self, unsafe=False):
        if unsafe:
            return self.roots['introduction'].decode_contents()  # return as HTML
        return self.roots['introduction'].get_text().strip()

    def get_learning_outcomes(self):
        if self.roots['learning_outcomes'] is None:
                return list()
        los_list = [
                self._fix_whitespace(text)
                for text in self.roots['learning_outcomes'].stripped_strings
                ]

        # Remove first line if it's introductory text
        if len(los_list) > 0 and (
                los_list[0].startswith("Upon completion")
                or los_list[0].startswith("Upon successful completion")
                or los_list[0].startswith("After completing")
                or los_list[0].startswith("In this course")):
            los_list.pop(0)

        # Remove last two lines if they're the link to the professional skills
        # mapping pages.
        if len(los_list) > 2 and los_list[-2].startswith("Profe"):
                los_list = los_list[:-2]

        # Remove list indices of the form "1. " at the start of outcomes
        los_list = [re.sub(r'^\d+\.\s+', '', lo) for lo in los_list]

        return los_list

#     def get_learning_outcomes_formatted(code):
#         out_lines = get_learning_outcomes(code)
#    
#         # Add numbering for formatting if not already present
#         # NB: Assumes exactly one line of introductory text such as
#         # "At the end of this course a student can:" or similar.
#         for i, line in enumerate(out_lines):
#             if not re.search('^\d', line) and i >= 1:
#                 line = str(i) + ". " + line
#                 out_lines[i] = line
#    
#         return out_lines

    def get_indicative_assessments(self):
        if self.roots['indicative_assessments'] is None:
            return self.roots['indicative_assessments']

        # We're treating IAs as pretty simple text strings now.
        txt = list(self.roots['indicative_assessments'].stripped_strings)
        # Strip out everything from the Turnitin statement onward
        turnitin = 'The ANU uses Turnitin'
        txt = txt[:next(iter([i for i, line in enumerate(txt) if line.startswith(turnitin)]), -1)]
        return txt

    def get_workload(self):
        if self.roots['workload'] is None:
                return self.roots['workload']
        return self._join_strings(self.roots['workload'].stripped_strings)

    def get_prescribed_texts(self, unsafe=False):
        if self.roots['prescribed_texts'] is None:
            return self.roots['prescribed_texts']
        elif unsafe:
            return self.roots['prescribed_texts'].decode_contents()  # return as HTML
        return self._join_strings(self.roots['prescribed_texts'].stripped_strings)

    def get_other_information(self, unsafe=False):
        if self.roots['other_information'] is None:
            return self.roots['other_information']
        elif unsafe:
            return self.roots['other_information'].decode_contents()  # return as HTML
        return self._join_strings(self.roots['other_information'].stripped_strings)

    def get_mode(self):
        return self.get_summary_detail("Mode of delivery")

    def get_convener(self):
        return self.get_summary_detail("Course convener")

    def get_offered_by(self):
        return self.get_summary_detail("Offered by")

    def get_req_and_incomp(self):
        if self.roots['req_and_incomp'] is None:
            return self.roots['req_and_incomp']
        return self._fix_whitespace(self.roots['req_and_incomp'].get_text())

    def get_course_dict(self):
            return {
                "code": self.code,
                "title": self.get_title(),
                "introduction": self.get_introduction() or "",
                "learning_outcomes": self.get_learning_outcomes() or [],
                "indicative_assessments": self.get_indicative_assessments(),
                "workload": self.get_workload() or "",
                "mode": self.get_mode(),
                "conveners": self.get_convener(),
                "req_and_incompat": self.get_req_and_incomp() or "",
                "offerings": self.get_offerings_all() or {},
                "prescribed_texts": self.get_prescribed_texts() or "",
                "offered_by": self.get_offered_by(),
                "other_information": self.get_other_information() or "",
            }