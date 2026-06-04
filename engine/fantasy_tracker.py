#!/opt/homebrew/bin/python3.11
"""
Fantasy Baseball In-Season Tracker

Tracks rest-of-season projection changes from FanGraphs,
integrates with ESPN for roster/free agent status, and
generates an HTML report with movement alerts.

Usage:
  python3.11 fantasy_tracker.py              # Fetch data, generate report
  python3.11 fantasy_tracker.py --setup      # Configure ESPN authentication

Daily Workflow:
  1. Run: python3.11 fantasy_tracker.py
  2. Open tracker_report.html
  3. Check risers/fallers, review free agent pickups
"""

import requests
import pandas as pd
from rapidfuzz import fuzz, process
import unicodedata
import json
import time
import sys
import os
import re
import math
import argparse
import fnmatch
import subprocess
from datetime import datetime, date, timedelta
from concurrent.futures import ThreadPoolExecutor, as_completed
from collections import Counter, defaultdict

# =============================================================================
# CONFIGURATION
# =============================================================================

NUM_TEAMS = 10
ESPN_LEAGUE_ID = "1067859015"
ESPN_TEAM_ID = 10  # "One Cruz Over the Cuckoo's Nest"

SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
TRACKER_DIR = os.path.join(SCRIPT_DIR, "tracker_snapshots")
CONFIG_FILE = os.path.join(SCRIPT_DIR, "tracker_config.json")
OUTPUT_HTML = os.path.join(SCRIPT_DIR, "tracker_report.html")
LOCAL_PREVIEW_DIR = os.path.join(SCRIPT_DIR, "local_preview")
PREVIEW_LOCAL = False
HITTER_DECISIONS_DIR = os.path.join(SCRIPT_DIR, "hitter_decisions")
WAREHOUSE_DIR = os.path.join(SCRIPT_DIR, "warehouse")
WAREHOUSE_LAYERS = ("raw", "clean", "features", "predictions", "outcomes", "views")

# FanGraphs Auction Calculator API (RoS projections)
FG_AUCTION_URL = "https://www.fangraphs.com/api/fantasy/auction-calculator/data"
FG_ROS_PARAMS = {
    'teams': 10, 'lg': 'MLB', 'dollars': 260, 'mb': 1, 'mp': 20,
    'msp': 5, 'mrp': 5, 'players': '', 'split': '',
    'points': 'p|0,0,0,1,2,3,4,1,0,1,1,1,-1,0,0,0|3,5,-5,5,1,-2,0,-1,0,-1,0',
    'rep': 0, 'drp': 0, 'pp': 'C,SS,2B,3B,OF,1B',
    'pos': '1,1,1,1,5,1,1,1,0,1,0,0,7,0,0',
    'sort': '', 'view': 0,
}

HEADERS = {
    'User-Agent': 'Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36',
    'Accept': 'application/json',
}

# ESPN API
ESPN_PLAYERS_URL = "https://lm-api-reads.fantasy.espn.com/apis/v3/games/flb/seasons/2026/players?scoringPeriodId=0&view=players_wl"

ESPN_TEAM_MAP = {
    0: 'FA', 1: 'BAL', 2: 'BOS', 3: 'LAA', 4: 'CWS', 5: 'CLE', 6: 'DET',
    7: 'KC', 8: 'MIL', 9: 'MIN', 10: 'NYY', 11: 'OAK', 12: 'PIT', 13: 'TEX',
    14: 'TOR', 15: 'ATL', 16: 'CHC', 17: 'CIN', 18: 'HOU', 19: 'LAD', 20: 'WSH',
    21: 'NYM', 22: 'PHI', 23: 'STL', 24: 'SD', 25: 'SF', 26: 'SEA', 27: 'AZ',
    28: 'TB', 29: 'COL', 30: 'MIA'
}

FG_TEAM_TO_ESPN = {
    'ATH': 'OAK', 'KCR': 'KC', 'SFG': 'SF', 'SDP': 'SD',
    'TBR': 'TB', 'WSN': 'WSH', 'CHW': 'CWS', 'ARI': 'AZ',
}

ESPN_POS_MAP = {
    1: 'SP', 2: 'C', 3: '1B', 4: '2B', 5: '3B',
    6: 'SS', 7: 'LF', 8: 'CF', 9: 'RF', 10: 'DH', 11: 'RP'
}
ESPN_LINEUP_SLOT_MAP = {
    0: 'C', 1: '1B', 2: '2B', 3: '3B', 4: 'SS',
    5: 'OF', 6: '2B/SS', 7: '1B/3B', 8: 'LF', 9: 'CF',
    10: 'RF', 11: 'DH', 12: 'UTIL', 13: 'P', 14: 'SP',
    15: 'RP', 16: 'BE', 17: 'IL', 18: 'IL', 19: 'IL',
    20: 'IL', 21: 'IL', 22: 'IL', 23: 'IL', 24: 'IL',
}
ESPN_BENCH_SLOT_IDS = {16}
ESPN_INJURY_SLOT_IDS = {17, 18, 19, 20, 21, 22, 23, 24}

PREMIUM_POS_ORDER = ['C', 'SS', '2B', '3B', 'OF', '1B', 'DH']

# MLB StatsAPI team ID -> abbreviation (matches ESPN abbreviations)
MLB_TEAM_TO_ABBR = {
    108: 'LAA', 109: 'AZ', 110: 'BAL', 111: 'BOS', 112: 'CHC',
    113: 'CIN', 114: 'CLE', 115: 'COL', 116: 'DET', 117: 'HOU',
    118: 'KC', 119: 'LAD', 120: 'WSH', 121: 'NYM', 133: 'OAK',
    134: 'PIT', 135: 'SD', 136: 'SEA', 137: 'SF', 138: 'STL',
    139: 'TB', 140: 'TEX', 141: 'TOR', 142: 'MIN', 143: 'PHI',
    144: 'ATL', 145: 'CWS', 146: 'MIA', 147: 'NYY', 158: 'MIL',
}
ABBR_TO_MLB_TEAM = {v: k for k, v in MLB_TEAM_TO_ABBR.items()}

# Streaming cache directory
STREAMING_CACHE_DIR = os.path.join(SCRIPT_DIR, "streaming_cache")
ROSTER_STATUS_CACHE_FILE = os.path.join(STREAMING_CACHE_DIR, "roster_status_cache.json")
_runtime_prediction_records = []
OPEN_METEO_WEATHER_CACHE_FILE = 'open_meteo_weather.json'
_open_meteo_weather_cache = None
PITCHER_WORKLOAD_HISTORY_CACHE_FILE = 'pitcher_workload_history.json'

# Pitching scoring weights (for per-start calculation)
PIT_SCORING = {'IP': 3, 'H': -1, 'ER': -2, 'BB': -1, 'K': 1, 'W': 5, 'L': -5}

# Park factors for run scoring (1.0 = neutral). Home team determines park.
# Source: multi-year averages from FanGraphs. Higher = more hitter-friendly.
PARK_FACTORS = {
    'COL': 1.35, 'CIN': 1.08, 'TEX': 1.07, 'AZ': 1.06, 'BOS': 1.05,
    'BAL': 1.04, 'PHI': 1.04, 'CHC': 1.03, 'ATL': 1.03, 'MIL': 1.02,
    'MIN': 1.02, 'LAD': 1.01, 'CLE': 1.00, 'NYY': 1.00, 'STL': 1.00,
    'HOU': 0.99, 'TOR': 0.99, 'DET': 0.99, 'KC': 0.98, 'CWS': 0.98,
    'WSH': 0.98, 'LAA': 0.97, 'PIT': 0.97, 'NYM': 0.96, 'SF': 0.96,
    'SD': 0.95, 'TB': 0.95, 'SEA': 0.95, 'MIA': 0.94, 'ATH': 0.96,
}

# Regression constant for opponent quality: PA worth of data before current season
# gets 50% weight. Higher = more regression toward league average early on.
OPP_REGRESS_PA = 800

# Recent-form trend labels feed learned hot/cold correction buckets. Keep the
# threshold higher than one good/bad turn so tiny samples do not move points.
RECENT_TREND_MIN_STARTS = 3
RECENT_TREND_MIN_IP_FALLBACK = 15.0

NAME_OVERRIDES = {}


# =============================================================================
# NAME MATCHING (shared logic with draft ranker)
# =============================================================================

def normalize_name(name):
    # Guard against NaN/float/None — pandas can yield NaN for missing names
    if name is None or not isinstance(name, str) or not name:
        return ""
    if name in NAME_OVERRIDES:
        name = NAME_OVERRIDES[name]
    nfkd = unicodedata.normalize('NFKD', name)
    ascii_name = ''.join(c for c in nfkd if not unicodedata.combining(c))
    ascii_name = ascii_name.lower().strip()
    ascii_name = re.sub(r'\s+(jr\.?|sr\.?|ii|iii|iv)\s*$', '', ascii_name)
    ascii_name = ascii_name.replace('.', '')
    ascii_name = ascii_name.replace("'", '').replace("\u2019", '').replace("\u2018", '')
    ascii_name = re.sub(r'\s+', ' ', ascii_name).strip()
    return ascii_name


def _venue_lookup_key(name):
    """Normalize MLB venue names for logged-only metadata lookup."""
    if not name:
        return ''
    return re.sub(r'[^a-z0-9]+', ' ', str(name).lower()).strip()


MLB_VENUE_METADATA_BY_TEAM = {
    'LAA': {'venue_name': 'Angel Stadium', 'venue_lat': 33.8003, 'venue_lon': -117.8827, 'roof_type': 'outdoor', 'is_indoor_or_dome': False, 'aliases': ['Angel Stadium of Anaheim']},
    'AZ': {'venue_name': 'Chase Field', 'venue_lat': 33.4455, 'venue_lon': -112.0667, 'roof_type': 'retractable', 'is_indoor_or_dome': True},
    'BAL': {'venue_name': 'Oriole Park at Camden Yards', 'venue_lat': 39.2839, 'venue_lon': -76.6217, 'roof_type': 'outdoor', 'is_indoor_or_dome': False, 'aliases': ['Camden Yards']},
    'BOS': {'venue_name': 'Fenway Park', 'venue_lat': 42.3467, 'venue_lon': -71.0972, 'roof_type': 'outdoor', 'is_indoor_or_dome': False},
    'CHC': {'venue_name': 'Wrigley Field', 'venue_lat': 41.9484, 'venue_lon': -87.6553, 'roof_type': 'outdoor', 'is_indoor_or_dome': False},
    'CIN': {'venue_name': 'Great American Ball Park', 'venue_lat': 39.0979, 'venue_lon': -84.5082, 'roof_type': 'outdoor', 'is_indoor_or_dome': False},
    'CLE': {'venue_name': 'Progressive Field', 'venue_lat': 41.4962, 'venue_lon': -81.6852, 'roof_type': 'outdoor', 'is_indoor_or_dome': False},
    'COL': {'venue_name': 'Coors Field', 'venue_lat': 39.7561, 'venue_lon': -104.9942, 'roof_type': 'outdoor', 'is_indoor_or_dome': False},
    'DET': {'venue_name': 'Comerica Park', 'venue_lat': 42.3390, 'venue_lon': -83.0485, 'roof_type': 'outdoor', 'is_indoor_or_dome': False},
    'HOU': {'venue_name': 'Daikin Park', 'venue_lat': 29.7573, 'venue_lon': -95.3555, 'roof_type': 'retractable', 'is_indoor_or_dome': True, 'aliases': ['Minute Maid Park']},
    'KC': {'venue_name': 'Kauffman Stadium', 'venue_lat': 39.0517, 'venue_lon': -94.4803, 'roof_type': 'outdoor', 'is_indoor_or_dome': False},
    'LAD': {'venue_name': 'Dodger Stadium', 'venue_lat': 34.0739, 'venue_lon': -118.2400, 'roof_type': 'outdoor', 'is_indoor_or_dome': False},
    'WSH': {'venue_name': 'Nationals Park', 'venue_lat': 38.8730, 'venue_lon': -77.0074, 'roof_type': 'outdoor', 'is_indoor_or_dome': False},
    'NYM': {'venue_name': 'Citi Field', 'venue_lat': 40.7571, 'venue_lon': -73.8458, 'roof_type': 'outdoor', 'is_indoor_or_dome': False},
    'OAK': {'venue_name': 'Sutter Health Park', 'venue_lat': 38.5803, 'venue_lon': -121.5139, 'roof_type': 'outdoor', 'is_indoor_or_dome': False},
    'PIT': {'venue_name': 'PNC Park', 'venue_lat': 40.4469, 'venue_lon': -80.0057, 'roof_type': 'outdoor', 'is_indoor_or_dome': False},
    'SD': {'venue_name': 'Petco Park', 'venue_lat': 32.7073, 'venue_lon': -117.1566, 'roof_type': 'outdoor', 'is_indoor_or_dome': False},
    'SEA': {'venue_name': 'T-Mobile Park', 'venue_lat': 47.5914, 'venue_lon': -122.3325, 'roof_type': 'retractable', 'is_indoor_or_dome': True, 'aliases': ['T Mobile Park', 'Safeco Field']},
    'SF': {'venue_name': 'Oracle Park', 'venue_lat': 37.7786, 'venue_lon': -122.3893, 'roof_type': 'outdoor', 'is_indoor_or_dome': False},
    'STL': {'venue_name': 'Busch Stadium', 'venue_lat': 38.6226, 'venue_lon': -90.1928, 'roof_type': 'outdoor', 'is_indoor_or_dome': False},
    'TB': {'venue_name': 'George M. Steinbrenner Field', 'venue_lat': 27.9802, 'venue_lon': -82.5065, 'roof_type': 'outdoor', 'is_indoor_or_dome': False, 'aliases': ['Tropicana Field']},
    'TEX': {'venue_name': 'Globe Life Field', 'venue_lat': 32.7473, 'venue_lon': -97.0842, 'roof_type': 'retractable', 'is_indoor_or_dome': True},
    'TOR': {'venue_name': 'Rogers Centre', 'venue_lat': 43.6414, 'venue_lon': -79.3894, 'roof_type': 'retractable', 'is_indoor_or_dome': True},
    'MIN': {'venue_name': 'Target Field', 'venue_lat': 44.9817, 'venue_lon': -93.2776, 'roof_type': 'outdoor', 'is_indoor_or_dome': False},
    'PHI': {'venue_name': 'Citizens Bank Park', 'venue_lat': 39.9058, 'venue_lon': -75.1665, 'roof_type': 'outdoor', 'is_indoor_or_dome': False},
    'ATL': {'venue_name': 'Truist Park', 'venue_lat': 33.8907, 'venue_lon': -84.4677, 'roof_type': 'outdoor', 'is_indoor_or_dome': False},
    'CWS': {'venue_name': 'Rate Field', 'venue_lat': 41.8300, 'venue_lon': -87.6338, 'roof_type': 'outdoor', 'is_indoor_or_dome': False, 'aliases': ['Guaranteed Rate Field', 'U.S. Cellular Field']},
    'MIA': {'venue_name': 'loanDepot park', 'venue_lat': 25.7781, 'venue_lon': -80.2197, 'roof_type': 'retractable', 'is_indoor_or_dome': True, 'aliases': ['loanDepot Park', 'Marlins Park']},
    'MIL': {'venue_name': 'American Family Field', 'venue_lat': 43.0280, 'venue_lon': -87.9712, 'roof_type': 'retractable', 'is_indoor_or_dome': True, 'aliases': ['Miller Park']},
}

MLB_VENUE_METADATA_BY_NAME = {}
for _team, _meta in MLB_VENUE_METADATA_BY_TEAM.items():
    for _name in [_meta.get('venue_name')] + list(_meta.get('aliases') or []):
        MLB_VENUE_METADATA_BY_NAME[_venue_lookup_key(_name)] = _meta
MLB_VENUE_METADATA_BY_NAME[_venue_lookup_key('Tropicana Field')] = {
    'venue_name': 'Tropicana Field',
    'venue_lat': 27.7683,
    'venue_lon': -82.6534,
    'roof_type': 'dome',
    'is_indoor_or_dome': True,
}


def _mlb_venue_metadata(team=None, venue_name=None):
    """Return logged-only static MLB park metadata when schedule names identify it."""
    meta = MLB_VENUE_METADATA_BY_NAME.get(_venue_lookup_key(venue_name))
    if meta:
        return meta
    return MLB_VENUE_METADATA_BY_TEAM.get(team or '', {})


def _home_team_for_record(record):
    if (record or {}).get('home_away') == 'H':
        return (record or {}).get('team')
    return (record or {}).get('opponent')


def _features_with_venue_metadata(features, record=None):
    """Fill missing venue lat/lon/roof feature fields without touching scoring."""
    out = dict(features or {})
    meta = _mlb_venue_metadata(
        team=_home_team_for_record(record or {}),
        venue_name=out.get('venue_name') or (record or {}).get('venue_name'),
    )
    if not meta:
        return out
    for key in ('venue_name', 'venue_lat', 'venue_lon', 'roof_type', 'is_indoor_or_dome'):
        if out.get(key) in (None, '') and meta.get(key) is not None:
            out[key] = meta.get(key)
    return out


def match_fg_to_espn(fg_players, espn_players):
    espn_by_normalized = {}
    for ep in espn_players:
        norm = normalize_name(ep['fullName'])
        if norm not in espn_by_normalized:
            espn_by_normalized[norm] = []
        espn_by_normalized[norm].append(ep)

    espn_names_list = list(espn_by_normalized.keys())
    matches = {}
    unmatched = []

    for fg in fg_players:
        fg_name = fg.get('name') if isinstance(fg, dict) else fg['name']
        # Skip rows where FG returned a missing/NaN name
        if not isinstance(fg_name, str) or not fg_name.strip():
            continue
        fg_norm = normalize_name(fg_name)
        fg_team = fg.get('team', '')
        fg_team_abbr = FG_TEAM_TO_ESPN.get(fg_team, fg_team)
        fg_type = fg.get('type', '')
        matched = False

        if fg_norm in espn_by_normalized:
            candidates = espn_by_normalized[fg_norm]
            if len(candidates) == 1:
                ep = candidates[0]
                matches[fg_name] = {
                    'espn_id': ep['id'], 'espn_name': ep['fullName'],
                    'score': 100, 'method': 'exact'
                }
                matched = True
            else:
                for ep in candidates:
                    ep_team = ESPN_TEAM_MAP.get(ep['proTeamId'], '')
                    if ep_team == fg_team_abbr:
                        matches[fg_name] = {
                            'espn_id': ep['id'], 'espn_name': ep['fullName'],
                            'score': 100, 'method': 'exact+team'
                        }
                        matched = True
                        break
                if not matched:
                    fg_positions = fg.get('positions', [])
                    for ep in candidates:
                        ep_pos = ESPN_POS_MAP.get(ep['defaultPositionId'], '')
                        ep_pos_general = 'OF' if ep_pos in ('LF', 'CF', 'RF') else ep_pos
                        if ep_pos_general in fg_positions or ep_pos in fg_positions:
                            matches[fg_name] = {
                                'espn_id': ep['id'], 'espn_name': ep['fullName'],
                                'score': 95, 'method': 'exact+pos'
                            }
                            matched = True
                            break
                if not matched:
                    for ep in candidates:
                        ep_pos = ESPN_POS_MAP.get(ep['defaultPositionId'], '')
                        is_pitcher = ep_pos in ('SP', 'RP')
                        fg_is_pitcher = fg_type == 'pitcher'
                        if is_pitcher == fg_is_pitcher:
                            matches[fg_name] = {
                                'espn_id': ep['id'], 'espn_name': ep['fullName'],
                                'score': 90, 'method': 'exact+postype'
                            }
                            matched = True
                            break

        if not matched:
            result = process.extractOne(
                fg_norm, espn_names_list,
                scorer=fuzz.token_sort_ratio, score_cutoff=75
            )
            if result:
                matched_norm, score, _ = result
                candidates = espn_by_normalized.get(matched_norm, [])
                if candidates:
                    best = candidates[0]
                    for ep in candidates:
                        ep_team = ESPN_TEAM_MAP.get(ep['proTeamId'], '')
                        if ep_team == fg_team_abbr:
                            best = ep
                            break
                    matches[fg_name] = {
                        'espn_id': best['id'], 'espn_name': best['fullName'],
                        'score': score, 'method': 'fuzzy'
                    }
                    matched = True

        if not matched:
            unmatched.append(fg_name)

    return matches, unmatched


def reconcile_with_roster(espn_matches, roster_map, espn_players):
    """Fix stale ESPN IDs by cross-referencing with actual roster data.

    If a matched ESPN ID isn't found in the roster map, search for an
    alternative ESPN entry with the same name that IS in the roster map.
    Fixes cases like Pivetta where cached ESPN data has a stale team/ID.
    """
    if not roster_map:
        return espn_matches

    espn_by_name = {}
    for ep in espn_players:
        norm = normalize_name(ep['fullName'])
        if norm not in espn_by_name:
            espn_by_name[norm] = []
        espn_by_name[norm].append(ep)

    updated = dict(espn_matches)
    fixed = []
    for fg_name, match in espn_matches.items():
        eid = match['espn_id']
        if eid not in roster_map:
            norm = normalize_name(fg_name)
            candidates = espn_by_name.get(norm, [])
            for ep in candidates:
                if ep['id'] in roster_map and ep['id'] != eid:
                    updated[fg_name] = {
                        'espn_id': ep['id'], 'espn_name': ep['fullName'],
                        'score': match['score'], 'method': match['method'] + '+roster'
                    }
                    fixed.append(f"{fg_name}: {eid} -> {ep['id']}")
                    break

    if fixed:
        print(f"  Reconciled {len(fixed)} IDs with roster data: {fixed}")
    return updated


def _player_status_from_roster(espn_id, roster_map):
    if not roster_map:
        return None
    if espn_id in roster_map:
        info = roster_map[espn_id]
        return 'MY ROSTER' if info.get('team_id') == ESPN_TEAM_ID else 'OTHER'
    return 'FA' if espn_id else None


def save_roster_status_cache(players_list, espn_matches, roster_map):
    """Persist non-sensitive local roster ownership for read-only audits."""
    if not roster_map:
        print("  Roster/status cache not written: ESPN roster data unavailable")
        return None
    rows = []
    updated_at = datetime.now().isoformat(timespec='seconds')
    for player in players_list or []:
        name = player.get('name')
        if not name:
            continue
        match = espn_matches.get(name, {}) if espn_matches else {}
        espn_id = player.get('espn_id') or match.get('espn_id')
        status = _player_status_from_roster(espn_id, roster_map)
        if not status:
            status = 'UNKNOWN'
        rows.append({
            'name': name,
            'normalized_name': normalize_name(name),
            'espn_id': espn_id,
            'mlb_id': player.get('mlb_id') or player.get('pitcher_mlb_id'),
            'team': player.get('team') or '',
            'status': status,
            'fantasy_status': status,
            'timestamp': updated_at,
        })
    payload = {
        'updated_at': updated_at,
        'source': 'local ESPN roster/status reconciliation',
        'players': rows,
    }
    try:
        os.makedirs(STREAMING_CACHE_DIR, exist_ok=True)
        with open(ROSTER_STATUS_CACHE_FILE, 'w') as f:
            json.dump(payload, f, indent=2, sort_keys=True)
        mode = 'local preview' if PREVIEW_LOCAL else 'normal run'
        print(f"  Roster/status cache written ({mode}): {len(rows)} rows -> {ROSTER_STATUS_CACHE_FILE}")
        return ROSTER_STATUS_CACHE_FILE
    except Exception as e:
        print(f"  Roster/status cache write failed: {type(e).__name__}: {e}")
        return None


# =============================================================================
# DATA FETCHING
# =============================================================================

def fetch_fg_ros_data(player_type, proj_system):
    label = "hitter" if player_type == "bat" else "pitcher"
    print(f"Fetching FG RoS auction values ({proj_system}, {label}s)...")
    params = {**FG_ROS_PARAMS, 'type': player_type, 'proj': proj_system}
    resp = requests.get(FG_AUCTION_URL, params=params, headers=HEADERS, timeout=30)
    resp.raise_for_status()
    data = resp.json()['data']
    pos_dollar = sum(1 for p in data if p.get('Dollars', 0) > 0)
    print(f"  Retrieved {len(data)} {label}s ({pos_dollar} above replacement)")
    return data


def fetch_espn_players():
    cache_file = os.path.join(SCRIPT_DIR, 'espn_players.json')
    if os.path.exists(cache_file):
        age_hours = (time.time() - os.path.getmtime(cache_file)) / 3600
        if age_hours < 24:
            print(f"Using cached ESPN players ({age_hours:.1f}h old)")
            with open(cache_file, 'r') as f:
                return json.load(f)

    print("Fetching ESPN player database...")
    espn_headers = {
        'User-Agent': 'Mozilla/5.0',
        'x-fantasy-filter': json.dumps({
            'players': {
                'limit': 5000,
                'sortDraftRanks': {
                    'sortPriority': 100, 'sortAsc': True, 'value': 'STANDARD'
                }
            }
        }),
    }
    resp = requests.get(ESPN_PLAYERS_URL, headers=espn_headers, timeout=60)
    resp.raise_for_status()
    data = resp.json()
    active = [p for p in data if p.get('eligibleSlots')]
    print(f"  Retrieved {len(data)} total, {len(active)} with position eligibility")
    if PREVIEW_LOCAL:
        print("  Local preview mode: skipping ESPN player cache write")
        return active
    with open(cache_file, 'w') as f:
        json.dump(active, f)
    return active


def load_config():
    if os.path.exists(CONFIG_FILE):
        with open(CONFIG_FILE, 'r') as f:
            return json.load(f)
    return {}


def fetch_espn_rosters(config):
    """Fetch league roster data. Returns {espn_player_id: {'team_name': str, 'team_id': int}} or None."""
    espn_s2 = config.get('espn_s2', '')
    swid = config.get('SWID', '') or config.get('swid', '')
    if not espn_s2 or not swid:
        return None

    print("Fetching ESPN league rosters...")
    url = f"https://lm-api-reads.fantasy.espn.com/apis/v3/games/flb/seasons/2026/segments/0/leagues/{ESPN_LEAGUE_ID}"
    try:
        resp = requests.get(
            url,
            params={'view': 'mRoster'},
            headers={'User-Agent': 'Mozilla/5.0'},
            cookies={'espn_s2': espn_s2, 'SWID': swid},
            timeout=30
        )
        if resp.status_code in (401, 403):
            print("  ESPN auth failed — cookies may be expired. Run: python3.11 fantasy_tracker.py --setup")
            return None
        resp.raise_for_status()
    except requests.RequestException as e:
        print(f"  ESPN roster fetch failed: {e}")
        return None

    data = resp.json()
    roster_map = {}
    teams = data.get('teams', [])
    for team in teams:
        team_id = team.get('id')
        # ESPN team names can be in different fields
        team_name = team.get('name', '') or f"{team.get('location', '')} {team.get('nickname', '')}".strip()
        entries = team.get('roster', {}).get('entries', [])
        for entry in entries:
            pid = entry.get('playerId')
            if pid:
                roster_map[pid] = {'team_name': team_name, 'team_id': team_id}

    print(f"  Found {len(roster_map)} rostered players across {len(teams)} teams")

    # Supplement with recent transactions (roster view can lag behind executed adds)
    try:
        resp2 = requests.get(
            url,
            params={'view': 'mTransactions2'},
            headers={'User-Agent': 'Mozilla/5.0'},
            cookies={'espn_s2': espn_s2, 'SWID': swid},
            timeout=30
        )
        resp2.raise_for_status()
        txns = resp2.json().get('transactions', [])
        patched = 0
        for tx in txns:
            if tx.get('status') != 'EXECUTED':
                continue
            for item in tx.get('items', []):
                pid = item.get('playerId')
                if not pid:
                    continue
                # Only patch ADDs missing from roster (handles API lag)
                if item.get('type') == 'ADD' and pid not in roster_map:
                    to_team = item.get('toTeamId', 0)
                    tname = ''
                    for t in teams:
                        if t.get('id') == to_team:
                            tname = t.get('name', '') or f"{t.get('location', '')} {t.get('nickname', '')}".strip()
                            break
                    roster_map[pid] = {'team_name': tname, 'team_id': to_team}
                    patched += 1
        if patched:
            print(f"  Patched {patched} roster entries from recent transactions")
    except Exception:
        pass  # Non-critical, roster view is the primary source

    return roster_map


def _espn_auth_parts(config):
    espn_s2 = (config or {}).get('espn_s2', '')
    swid = (config or {}).get('SWID', '') or (config or {}).get('swid', '')
    if not espn_s2 or not swid:
        return None
    return {
        'headers': {'User-Agent': 'Mozilla/5.0'},
        'cookies': {'espn_s2': espn_s2, 'SWID': swid},
    }


def _espn_league_url():
    return f"https://lm-api-reads.fantasy.espn.com/apis/v3/games/flb/seasons/2026/segments/0/leagues/{ESPN_LEAGUE_ID}"


def fetch_espn_league_payload(config, views=None, scoring_period_id=None):
    """Read-only ESPN league payload using the same stored session cookies."""
    auth = _espn_auth_parts(config)
    if not auth:
        return None, "missing ESPN auth; run --setup"
    params = []
    for view in views or []:
        params.append(('view', view))
    if scoring_period_id is not None:
        params.append(('scoringPeriodId', scoring_period_id))
    try:
        resp = requests.get(
            _espn_league_url(),
            params=params,
            headers=auth['headers'],
            cookies=auth['cookies'],
            timeout=30,
        )
        if resp.status_code in (401, 403):
            return None, "ESPN auth failed; cookies may be expired"
        resp.raise_for_status()
        return resp.json(), None
    except requests.RequestException as e:
        return None, f"ESPN matchup fetch failed: {e}"


def _espn_team_name(team):
    if not isinstance(team, dict):
        return ''
    return team.get('name') or f"{team.get('location', '')} {team.get('nickname', '')}".strip() or f"Team {team.get('id', '?')}"


def _espn_period_info(payload):
    status = (payload or {}).get('status') or {}
    return {
        'current_matchup_period': (
            status.get('currentMatchupPeriod')
            or status.get('currentMatchupPeriodId')
            or status.get('matchupPeriodId')
        ),
        'current_scoring_period': (
            status.get('currentScoringPeriod')
            or status.get('currentScoringPeriodId')
            or (payload or {}).get('scoringPeriodId')
        ),
        'latest_scoring_period': status.get('latestScoringPeriod'),
        'first_scoring_period': status.get('firstScoringPeriod'),
        'final_scoring_period': status.get('finalScoringPeriod'),
    }


def _espn_current_period(payload):
    info = _espn_period_info(payload)
    return info.get('current_scoring_period') or info.get('latest_scoring_period')


def _espn_box_score(entry):
    for key in ('totalPoints', 'totalPointsLive', 'appliedStatTotal', 'points', 'score'):
        val = _safe_float((entry or {}).get(key))
        if val is not None:
            return val
    return None


def _espn_schedule_team_id(side):
    if not isinstance(side, dict):
        return None
    return side.get('teamId') or (side.get('team') or {}).get('id')


def _espn_schedule_score_info(side, scoring_period_id=None):
    if not isinstance(side, dict):
        return None, None
    for key in ('totalPointsLive', 'totalPoints', 'appliedStatTotal', 'points', 'score'):
        value = side.get(key)
        val = _safe_float(value)
        if val is not None:
            return val, key
    value = side.get('pointsByScoringPeriod')
    if isinstance(value, dict):
        if scoring_period_id is not None:
            single = _safe_float(value.get(str(scoring_period_id)) or value.get(scoring_period_id))
            if single is not None:
                # Prefer weekly/period totals above; this single-day value is
                # only a fallback so we can show something diagnostic.
                return single, f'pointsByScoringPeriod[{scoring_period_id}]'
        vals = [_safe_float(v) for v in value.values()]
        vals = [v for v in vals if v is not None]
        if vals:
            return round(sum(vals), 2), 'pointsByScoringPeriod:sum'
    return None, None


def _espn_schedule_score(side):
    return _espn_schedule_score_info(side)[0]


def _espn_entry_scoring_periods(matchup):
    periods = set()
    for side_key in ('home', 'away'):
        points = ((matchup or {}).get(side_key) or {}).get('pointsByScoringPeriod')
        if isinstance(points, dict):
            for key in points.keys():
                try:
                    periods.add(int(key))
                except Exception:
                    periods.add(str(key))
    return periods


def _espn_schedule_matchup_period(matchup):
    return (
        (matchup or {}).get('matchupPeriodId')
        or (matchup or {}).get('matchupPeriod')
        or (matchup or {}).get('periodId')
    )


def _espn_schedule_scoring_period(matchup):
    return (
        (matchup or {}).get('scoringPeriodId')
        or (matchup or {}).get('scoringPeriod')
    )


def _espn_matchup_candidates(payload, my_team_id, scoring_period_id=None):
    teams = {team.get('id'): team for team in (payload or {}).get('teams', []) if team.get('id') is not None}
    scoring_period = scoring_period_id or _espn_period_info(payload).get('current_scoring_period')
    out = []
    for idx, matchup in enumerate((payload or {}).get('schedule') or []):
        sides = [matchup.get('home') or {}, matchup.get('away') or {}]
        team_ids = [_espn_schedule_team_id(side) for side in sides]
        if my_team_id not in team_ids:
            continue
        my_side = sides[0] if team_ids[0] == my_team_id else sides[1]
        opp_side = sides[1] if team_ids[0] == my_team_id else sides[0]
        my_score, my_score_source = _espn_schedule_score_info(my_side, scoring_period)
        opp_score, opp_score_source = _espn_schedule_score_info(opp_side, scoring_period)
        opp_id = _espn_schedule_team_id(opp_side)
        out.append({
            'index': idx,
            'id': matchup.get('id') or matchup.get('matchupId') or matchup.get('scheduleId'),
            'matchup': matchup,
            'matchup_period_id': _espn_schedule_matchup_period(matchup),
            'scoring_period_id': _espn_schedule_scoring_period(matchup),
            'scoring_periods': sorted(_espn_entry_scoring_periods(matchup), key=lambda v: str(v)),
            'winner': matchup.get('winner'),
            'status': matchup.get('status') or matchup.get('matchupStatus'),
            'home_team_id': team_ids[0],
            'away_team_id': team_ids[1],
            'home_team_name': _espn_team_name(teams.get(team_ids[0])),
            'away_team_name': _espn_team_name(teams.get(team_ids[1])),
            'home_score': _espn_schedule_score(sides[0]),
            'away_score': _espn_schedule_score(sides[1]),
            'my_score': my_score,
            'my_score_source': my_score_source,
            'opponent_team_id': opp_id,
            'opponent_team_name': _espn_team_name(teams.get(opp_id)),
            'opponent_score': opp_score,
            'opponent_score_source': opp_score_source,
        })
    return out


def _find_current_matchup(payload, my_team_id, period_info=None):
    period_info = period_info or _espn_period_info(payload)
    current_matchup_period = period_info.get('current_matchup_period')
    current_scoring_period = period_info.get('current_scoring_period')
    candidates = _espn_matchup_candidates(payload, my_team_id, current_scoring_period)
    if not candidates:
        return None

    def selected(candidate, method, confidence=True):
        out = dict(candidate)
        out['selection_method'] = method
        out['confidence'] = bool(confidence)
        return out

    if current_matchup_period is not None:
        exact = [c for c in candidates if str(c.get('matchup_period_id')) == str(current_matchup_period)]
        if len(exact) == 1:
            return selected(exact[0], 'currentMatchupPeriod')
        if len(exact) > 1:
            scored = [c for c in exact if c.get('my_score') is not None and c.get('opponent_score') is not None]
            if len(scored) == 1:
                return selected(scored[0], 'currentMatchupPeriod+score-fields')
            return {
                'confidence': False,
                'error': f"Multiple matchup entries matched currentMatchupPeriod={current_matchup_period}.",
                'candidates': exact,
            }

    if current_scoring_period is not None:
        mapped = [
            c for c in candidates
            if str(c.get('scoring_period_id')) == str(current_scoring_period)
            or current_scoring_period in c.get('scoring_periods', [])
            or str(current_scoring_period) in {str(v) for v in c.get('scoring_periods', [])}
        ]
        if len(mapped) == 1:
            return selected(mapped[0], 'currentScoringPeriod')
        if len(mapped) > 1:
            undecided = [c for c in mapped if str(c.get('winner') or '').upper() in ('', 'UNDECIDED')]
            if len(undecided) == 1:
                return selected(undecided[0], 'currentScoringPeriod+undecided')
            return {
                'confidence': False,
                'error': f"Multiple matchup entries matched currentScoringPeriod={current_scoring_period}.",
                'candidates': mapped,
            }

    undecided = [c for c in candidates if str(c.get('winner') or '').upper() in ('', 'UNDECIDED')]
    if len(undecided) == 1:
        return selected(undecided[0], 'single-undecided-matchup', confidence=True)
    if len(candidates) == 1:
        return selected(candidates[0], 'only-team-matchup-entry', confidence=False)
    return {
        'confidence': False,
        'error': 'Unable to identify current matchup confidently from ESPN schedule entries.',
        'candidates': candidates,
    }


def _espn_roster_player(entry):
    ppe = (entry or {}).get('playerPoolEntry') or {}
    player = ppe.get('player') or {}
    return player


def _espn_entry_name(entry):
    player = _espn_roster_player(entry)
    return player.get('fullName') or player.get('name') or f"Player {entry.get('playerId', '?')}"


def _espn_entry_pos(entry):
    player = _espn_roster_player(entry)
    default_pos = player.get('defaultPositionId')
    return ESPN_POS_MAP.get(default_pos, str(default_pos or ''))


def _espn_entry_injury(entry):
    player = _espn_roster_player(entry)
    status = player.get('injuryStatus') or player.get('injuryStatusAbbrev') or player.get('status')
    injured = player.get('injured')
    if status and str(status).upper() not in ('ACTIVE', 'NORMAL', 'OK'):
        return str(status)
    if injured:
        return 'injured'
    return ''


def _espn_roster_rows(team):
    rows = []
    entries = ((team or {}).get('roster') or {}).get('entries') or []
    for entry in entries:
        slot_id = entry.get('lineupSlotId')
        slot = ESPN_LINEUP_SLOT_MAP.get(slot_id, str(slot_id or '?'))
        row = {
            'name': _espn_entry_name(entry),
            'slot': slot,
            'slot_id': slot_id,
            'pos': _espn_entry_pos(entry),
            'team': ESPN_TEAM_MAP.get((_espn_roster_player(entry) or {}).get('proTeamId'), ''),
            'injury': _espn_entry_injury(entry),
            'points': _espn_box_score(entry),
        }
        rows.append(row)
    return rows


def _split_roster_rows(rows):
    active, bench, injured = [], [], []
    for row in rows:
        slot_id = row.get('slot_id')
        if slot_id in ESPN_INJURY_SLOT_IDS or row.get('injury'):
            injured.append(row)
        if slot_id in ESPN_BENCH_SLOT_IDS:
            bench.append(row)
        elif slot_id not in ESPN_INJURY_SLOT_IDS:
            active.append(row)
    return active, bench, injured


def _empty_lineup_slots(active_rows):
    # This is deliberately conservative: ESPN roster entries usually omit truly
    # empty slots, and league lineup rules can vary. Only report explicit empty
    # placeholder entries if ESPN sends them.
    return [r.get('slot') for r in active_rows if not r.get('name') or str(r.get('name')).startswith('Player ?')]


def _format_matchup_player(row):
    meta = []
    if row.get('slot'):
        meta.append(row['slot'])
    if row.get('pos'):
        meta.append(row['pos'])
    if row.get('team'):
        meta.append(row['team'])
    pts = row.get('points')
    pts_text = f" — {pts:.1f} pts" if pts is not None else ""
    injury = f" [{row['injury']}]" if row.get('injury') else ""
    meta_text = f" ({', '.join(meta)})" if meta else ""
    return f"{row.get('name') or 'Unknown'}{meta_text}{pts_text}{injury}"


def _print_matchup_list(title, rows, limit=18):
    print(f"\n{title}")
    if not rows:
        print("  None detected")
        return
    for row in rows[:limit]:
        print(f"  - {_format_matchup_player(row)}")
    if len(rows) > limit:
        print(f"  ... {len(rows) - limit} more")


def _merge_period_info(primary, fallback):
    primary = primary or {}
    fallback = fallback or {}
    return {key: primary.get(key) if primary.get(key) is not None else fallback.get(key)
            for key in set(primary) | set(fallback)}


def build_matchup_snapshot():
    """Return read-only current ESPN H2H matchup snapshot data."""
    config = load_config()
    payload, err = fetch_espn_league_payload(
        config,
        views=['mTeam', 'mRoster', 'mMatchup', 'mMatchupScore', 'mSettings'],
    )
    if err:
        return {'error': err}

    base_period_info = _espn_period_info(payload)
    period = base_period_info.get('current_scoring_period') or base_period_info.get('latest_scoring_period')
    period_info = dict(base_period_info)
    if period:
        period_payload, period_err = fetch_espn_league_payload(
            config,
            views=['mTeam', 'mRoster', 'mMatchup', 'mMatchupScore', 'mSettings'],
            scoring_period_id=period,
        )
        if not period_err and period_payload:
            payload = period_payload
            period_info = _merge_period_info(_espn_period_info(period_payload), base_period_info)

    teams = {team.get('id'): team for team in (payload.get('teams') or []) if team.get('id') is not None}
    my_team = teams.get(ESPN_TEAM_ID)
    if not my_team:
        return {
            'error': f"My team id {ESPN_TEAM_ID} was not found in the ESPN payload.",
            'available_teams': {tid: _espn_team_name(team) for tid, team in sorted(teams.items())},
        }

    matchup = _find_current_matchup(payload, ESPN_TEAM_ID, period_info)
    if not matchup or not matchup.get('confidence'):
        return {
            'error': 'Unable to identify current matchup confidently',
            'low_confidence': True,
            'period_info': period_info,
            'my_team': {'id': ESPN_TEAM_ID, 'name': _espn_team_name(my_team)},
            'available_fields': {
                'teams': len(teams),
                'schedule_entries': len(payload.get('schedule') or []),
                'my_roster_entries': len(_espn_roster_rows(my_team)),
                'opponent_roster_entries': 0,
                'score_fields': False,
            },
            'candidate_count': len((matchup or {}).get('candidates') or _espn_matchup_candidates(payload, ESPN_TEAM_ID, period_info.get('current_scoring_period'))),
            'selection_error': (matchup or {}).get('error'),
        }

    opponent_id = matchup.get('opponent_team_id') if matchup else None
    opponent = teams.get(opponent_id) if opponent_id is not None else None

    my_rows = _espn_roster_rows(my_team)
    opp_rows = _espn_roster_rows(opponent) if opponent else []
    my_active, my_bench, my_injured = _split_roster_rows(my_rows)
    opp_active, opp_bench, opp_injured = _split_roster_rows(opp_rows)
    my_empty = _empty_lineup_slots(my_active)
    opp_empty = _empty_lineup_slots(opp_active)

    my_score = matchup.get('my_score') if matchup else None
    opp_score = matchup.get('opponent_score') if matchup else None
    margin = round(my_score - opp_score, 2) if my_score is not None and opp_score is not None else None
    injury_notes = []
    for row in my_injured:
        injury_notes.append(f"MY: {_format_matchup_player(row)}")
    for row in opp_injured:
        injury_notes.append(f"OPP: {_format_matchup_player(row)}")
    for slot in my_empty:
        injury_notes.append(f"MY empty active slot: {slot}")
    for slot in opp_empty:
        injury_notes.append(f"OPP empty active slot: {slot}")
    snapshot = {
        'scoring_period': period_info.get('current_scoring_period') or period,
        'matchup_period': period_info.get('current_matchup_period'),
        'period_info': period_info,
        'confidence': True,
        'my_team': {'id': ESPN_TEAM_ID, 'name': _espn_team_name(my_team)},
        'opponent': {'id': opponent_id, 'name': _espn_team_name(opponent) if opponent else None},
        'score': {'mine': my_score, 'opponent': opp_score, 'margin': margin},
        'selected_matchup': {
            'selection_method': matchup.get('selection_method'),
            'schedule_index': matchup.get('index'),
            'entry_id': matchup.get('id'),
            'matchup_period_id': matchup.get('matchup_period_id'),
            'scoring_period_id': matchup.get('scoring_period_id') or period_info.get('current_scoring_period'),
            'winner': matchup.get('winner'),
            'status': matchup.get('status'),
            'my_score_source': matchup.get('my_score_source'),
            'opponent_score_source': matchup.get('opponent_score_source'),
        },
        'my_active': my_active,
        'my_bench': my_bench,
        'opponent_active': opp_active,
        'opponent_bench': opp_bench,
        'injury_notes': injury_notes,
        'empty_slots': {'mine': my_empty, 'opponent': opp_empty},
        'available_fields': {
            'teams': len(teams),
            'schedule_entries': len(payload.get('schedule') or []),
            'my_roster_entries': len(my_rows),
            'opponent_roster_entries': len(opp_rows),
            'score_fields': my_score is not None and opp_score is not None,
        },
    }
    return snapshot


def _print_matchup_snapshot(snapshot, include_actions=False):
    print("MATCHUP SNAPSHOT")
    print("=" * 60)
    if not snapshot or snapshot.get('error'):
        message = (snapshot or {}).get('error') or 'unknown error'
        print(f"Unable to load ESPN matchup data: {message}")
        if (snapshot or {}).get('low_confidence'):
            print("Unable to identify current matchup confidently")
            period_info = (snapshot or {}).get('period_info') or {}
            print(f"Selected matchupPeriodId: unavailable (current={period_info.get('current_matchup_period')})")
            print(f"Selected scoringPeriodId: unavailable (current={period_info.get('current_scoring_period')})")
            if (snapshot or {}).get('selection_error'):
                print(f"Selection detail: {snapshot.get('selection_error')}")
            print(f"Candidate entries involving my team: {(snapshot or {}).get('candidate_count', 0)}")
        if (snapshot or {}).get('available_teams'):
            print("Available teams:")
            for tid, name in snapshot['available_teams'].items():
                print(f"  - {tid}: {name}")
        print("No files were modified.")
        return

    my_team_name = (snapshot.get('my_team') or {}).get('name') or 'my team'
    opponent_name = (snapshot.get('opponent') or {}).get('name') or 'not available'
    score = snapshot.get('score') or {}
    my_score = score.get('mine')
    opp_score = score.get('opponent')
    margin = score.get('margin')
    print(f"Scoring period: {snapshot.get('scoring_period') or 'unknown'}")
    print(f"Matchup period: {snapshot.get('matchup_period') or 'unknown'}")
    print(f"My team: {my_team_name}")
    print(f"Opponent: {opponent_name}")
    if my_score is not None and opp_score is not None:
        print(f"Score: {my_team_name} {my_score:.1f} — {opponent_name} {opp_score:.1f}")
        print(f"Margin: {margin:+.1f}")
    else:
        print("Score: not available from current ESPN matchup payload")
        print("Margin: not available")

    selected = snapshot.get('selected_matchup') or {}
    print("\nSelected ESPN matchup")
    print(f"  - selection method: {selected.get('selection_method') or 'unknown'}")
    print(f"  - matchupPeriodId: {selected.get('matchup_period_id')}")
    print(f"  - scoringPeriodId: {selected.get('scoring_period_id')}")
    print(f"  - schedule entry: index={selected.get('schedule_index')} id={selected.get('entry_id')}")
    print(f"  - score sources: mine={selected.get('my_score_source') or 'missing'}, opponent={selected.get('opponent_score_source') or 'missing'}")

    _print_matchup_list("My active players", snapshot.get('my_active') or [])
    _print_matchup_list("Opponent active players", snapshot.get('opponent_active') or [])

    my_bench = snapshot.get('my_bench') or []
    bench_watch = [r for r in my_bench if r.get('injury') or r.get('points') is not None]
    if not bench_watch:
        bench_watch = my_bench[:8]
    _print_matchup_list("My bench watch items", bench_watch, limit=10)

    injury_notes = snapshot.get('injury_notes') or []
    _print_matchup_list("Injury / empty-slot notes", [{'name': note, 'slot': ''} for note in injury_notes], limit=12)

    fields = snapshot.get('available_fields') or {}
    print("\nAvailable ESPN matchup fields")
    print(f"  - teams: {fields.get('teams', 0)}")
    print(f"  - schedule/matchup entries: {fields.get('schedule_entries', 0)}")
    print(f"  - my roster entries: {fields.get('my_roster_entries', 0)}")
    print(f"  - opponent roster entries: {fields.get('opponent_roster_entries', 0)}")
    print(f"  - score fields: {'available' if fields.get('score_fields') else 'missing'}")

    print("\nMissing / TODO")
    if not (snapshot.get('opponent') or {}).get('id'):
        print("  - Current head-to-head matchup was not present in the ESPN schedule payload.")
    if my_score is None or opp_score is None:
        print("  - Live matchup score needs a richer ESPN boxscore/matchup helper if this view stays blank.")
    if not (snapshot.get('opponent') or {}).get('name'):
        print("  - Opponent roster requires resolving the current matchup opponent first.")
    empty_slots = snapshot.get('empty_slots') or {}
    if not empty_slots.get('mine') and not empty_slots.get('opponent'):
        print("  - Empty lineup slot detection is conservative; ESPN does not expose empty slots as roster entries here.")
    print("  - Win probability is not implemented yet.")

    if include_actions:
        actions = build_matchup_action_recommendations(snapshot)
        print_matchup_actions(actions)


def _print_matchup_payload_table(payload, label):
    period_info = _espn_period_info(payload)
    teams = {team.get('id'): team for team in (payload or {}).get('teams', []) if team.get('id') is not None}
    print(f"\n{label}")
    print("-" * 100)
    print(
        "status: "
        f"currentMatchupPeriod={period_info.get('current_matchup_period')} | "
        f"currentScoringPeriod={period_info.get('current_scoring_period')} | "
        f"latestScoringPeriod={period_info.get('latest_scoring_period')}"
    )
    candidates = _espn_matchup_candidates(
        payload,
        ESPN_TEAM_ID,
        period_info.get('current_scoring_period'),
    )
    if not candidates:
        print("No schedule entries involving my team found.")
        return
    print("idx  id     matchup  scoring  home                         away                         home_score        away_score        winner/status")
    for c in candidates:
        home = f"{c.get('home_team_id')} {_espn_team_name(teams.get(c.get('home_team_id')))}"[:28]
        away = f"{c.get('away_team_id')} {_espn_team_name(teams.get(c.get('away_team_id')))}"[:28]
        home_score = c.get('home_score')
        away_score = c.get('away_score')
        home_txt = f"{home_score:.1f}" if home_score is not None else "--"
        away_txt = f"{away_score:.1f}" if away_score is not None else "--"
        status = c.get('winner') or c.get('status') or ''
        print(
            f"{c.get('index')!s:<4} {str(c.get('id') or ''):<6} "
            f"{str(c.get('matchup_period_id') or ''):<8} "
            f"{str(c.get('scoring_period_id') or ''):<8} "
            f"{home:<28} {away:<28} "
            f"{home_txt:<17} {away_txt:<17} {status}"
        )


def debug_matchup_payload():
    """Read-only compact ESPN matchup payload diagnostic."""
    config = load_config()
    views = ['mTeam', 'mRoster', 'mMatchup', 'mMatchupScore', 'mSettings']
    payload, err = fetch_espn_league_payload(config, views=views)
    print("MATCHUP PAYLOAD DEBUG")
    print("=" * 60)
    if err:
        print(err)
        return
    _print_matchup_payload_table(payload, "Base league payload")
    period = _espn_period_info(payload).get('current_scoring_period') or _espn_period_info(payload).get('latest_scoring_period')
    if period:
        period_payload, period_err = fetch_espn_league_payload(config, views=views, scoring_period_id=period)
        if period_err:
            print(f"\nCurrent scoring period payload failed: {period_err}")
        else:
            _print_matchup_payload_table(period_payload, f"Payload with scoringPeriodId={period}")
    snapshot = build_matchup_snapshot()
    print("\nSelected snapshot")
    if snapshot.get('error'):
        print(f"  error: {snapshot.get('error')}")
        print(f"  selection_error: {snapshot.get('selection_error')}")
    else:
        selected = snapshot.get('selected_matchup') or {}
        print(f"  my team: {(snapshot.get('my_team') or {}).get('id')} {(snapshot.get('my_team') or {}).get('name')}")
        print(f"  opponent: {(snapshot.get('opponent') or {}).get('id')} {(snapshot.get('opponent') or {}).get('name')}")
        print(f"  matchupPeriodId: {selected.get('matchup_period_id')}")
        print(f"  scoringPeriodId: {selected.get('scoring_period_id')}")
        print(f"  schedule index/id: {selected.get('schedule_index')} / {selected.get('entry_id')}")
        print(f"  score sources: {selected.get('my_score_source')} / {selected.get('opponent_score_source')}")
    print("No files were modified.")


def matchup_snapshot():
    """Read-only current ESPN H2H matchup snapshot foundation."""
    snapshot = build_matchup_snapshot()
    _print_matchup_snapshot(snapshot, include_actions=True)
    return snapshot


# =============================================================================
# STREAMING: DATA FETCHING
# =============================================================================

def _load_streaming_cache(filename, max_age_hours=24):
    """Load a cached file if it exists and is fresh enough."""
    os.makedirs(STREAMING_CACHE_DIR, exist_ok=True)
    filepath = os.path.join(STREAMING_CACHE_DIR, filename)
    if os.path.exists(filepath):
        age_hours = (time.time() - os.path.getmtime(filepath)) / 3600
        if age_hours < max_age_hours:
            with open(filepath, 'r') as f:
                return json.load(f), age_hours
    return None, None


def _save_streaming_cache(filename, data):
    if PREVIEW_LOCAL:
        print(f"  Local preview mode: skipping cache write {filename}")
        return
    os.makedirs(STREAMING_CACHE_DIR, exist_ok=True)
    filepath = os.path.join(STREAMING_CACHE_DIR, filename)
    with open(filepath, 'w') as f:
        json.dump(data, f, indent=2)


def _parse_game_datetime_utc(value):
    if not value:
        return None
    try:
        return datetime.fromisoformat(str(value).replace('Z', '+00:00'))
    except Exception:
        return None


def _wind_direction_label(degrees):
    deg = _safe_float(degrees)
    if deg is None:
        return None
    directions = ['N', 'NNE', 'NE', 'ENE', 'E', 'ESE', 'SE', 'SSE',
                  'S', 'SSW', 'SW', 'WSW', 'W', 'WNW', 'NW', 'NNW']
    return directions[int((deg + 11.25) // 22.5) % 16]


def _weather_blank(note):
    return {
        'weather_source': None,
        'weather_snapshot_time': None,
        'weather_temp_f': None,
        'weather_wind_speed_mph': None,
        'weather_wind_direction': None,
        'wind_out_to_cf_score': None,
        'wind_in_from_cf_score': None,
        'wind_cross_score': None,
        'weather_precip_prob': None,
        'weather_humidity': None,
        'weather_pressure': None,
        'weather_run_boost': None,
        'weather_hr_boost': None,
        'weather_note': note,
    }


def _open_meteo_cache():
    global _open_meteo_weather_cache
    if _open_meteo_weather_cache is None:
        cached, _ = _load_streaming_cache(OPEN_METEO_WEATHER_CACHE_FILE, max_age_hours=12)
        _open_meteo_weather_cache = cached if isinstance(cached, dict) else {}
    return _open_meteo_weather_cache


def _open_meteo_cache_key(lat, lon, game_dt):
    return f"{round(float(lat), 4)}|{round(float(lon), 4)}|{game_dt.date().isoformat()}"


def _fetch_open_meteo_hourly(lat, lon, game_dt):
    cache = _open_meteo_cache()
    key = _open_meteo_cache_key(lat, lon, game_dt)
    cached = cache.get(key)
    if cached:
        return cached

    params = {
        'latitude': lat,
        'longitude': lon,
        'start_date': game_dt.date().isoformat(),
        'end_date': game_dt.date().isoformat(),
        'hourly': ','.join([
            'temperature_2m',
            'relative_humidity_2m',
            'precipitation_probability',
            'surface_pressure',
            'wind_speed_10m',
            'wind_direction_10m',
        ]),
        'temperature_unit': 'fahrenheit',
        'wind_speed_unit': 'mph',
        'timezone': 'UTC',
    }
    resp = requests.get('https://api.open-meteo.com/v1/forecast', params=params, timeout=20)
    resp.raise_for_status()
    payload = {
        'fetched_at': datetime.utcnow().isoformat(timespec='seconds') + 'Z',
        'data': resp.json(),
    }
    cache[key] = payload
    _save_streaming_cache(OPEN_METEO_WEATHER_CACHE_FILE, cache)
    return payload


def _hourly_weather_at_game_time(payload, game_dt):
    hourly = (payload or {}).get('data', {}).get('hourly') or {}
    times = hourly.get('time') or []
    if not times:
        return None
    target = game_dt.replace(tzinfo=None)
    best_idx = None
    best_delta = None
    for idx, raw_time in enumerate(times):
        try:
            hour_dt = datetime.fromisoformat(raw_time)
        except Exception:
            continue
        delta = abs((hour_dt - target).total_seconds())
        if best_delta is None or delta < best_delta:
            best_idx = idx
            best_delta = delta
    if best_idx is None:
        return None

    def value(name):
        values = hourly.get(name) or []
        if best_idx >= len(values):
            return None
        return values[best_idx]

    return {
        'temp_f': value('temperature_2m'),
        'wind_speed_mph': value('wind_speed_10m'),
        'wind_direction_degrees': value('wind_direction_10m'),
        'precip_prob': value('precipitation_probability'),
        'humidity': value('relative_humidity_2m'),
        'pressure': value('surface_pressure'),
    }


def _logged_outdoor_weather_snapshot(features):
    """Fetch pregame outdoor weather for logged-only analysis when clearly safe."""
    game_dt = _parse_game_datetime_utc(features.get('game_datetime'))
    if not game_dt:
        return _weather_blank('missing game_datetime')
    lat = _safe_float(features.get('venue_lat'))
    lon = _safe_float(features.get('venue_lon'))
    if lat is None or lon is None:
        return _weather_blank('missing venue coordinates')

    roof_type = str(features.get('roof_type') or 'unknown').lower()
    is_indoor = features.get('is_indoor_or_dome')
    if roof_type == 'dome' or (is_indoor is True and roof_type != 'outdoor'):
        return _weather_blank('indoor/dome or retractable-roof game; outdoor weather not assumed without roof status')
    if roof_type not in ('outdoor', 'unknown'):
        return _weather_blank('roof status unknown; outdoor weather not assumed')

    try:
        payload = _fetch_open_meteo_hourly(lat, lon, game_dt)
        weather = _hourly_weather_at_game_time(payload, game_dt)
        if not weather:
            return _weather_blank('Open-Meteo hourly weather unavailable for game time')
        wind_dir_degrees = weather.get('wind_direction_degrees')
        wind_label = _wind_direction_label(wind_dir_degrees)
        note = 'Open-Meteo hourly forecast at nearest game-time hour; wind-to-field orientation not modeled yet.'
        return {
            'weather_source': 'open-meteo',
            'weather_snapshot_time': payload.get('fetched_at'),
            'weather_temp_f': _safe_float(weather.get('temp_f')),
            'weather_wind_speed_mph': _safe_float(weather.get('wind_speed_mph')),
            'weather_wind_direction': wind_label,
            'wind_out_to_cf_score': None,
            'wind_in_from_cf_score': None,
            'wind_cross_score': None,
            'weather_precip_prob': _safe_float(weather.get('precip_prob')),
            'weather_humidity': _safe_float(weather.get('humidity')),
            'weather_pressure': _safe_float(weather.get('pressure')),
            'weather_run_boost': None,
            'weather_hr_boost': None,
            'weather_note': note,
        }
    except Exception as e:
        return _weather_blank(f'weather unavailable: {type(e).__name__}')


def _features_with_weather_metadata(features, record=None):
    """Fill logged-only weather fields for prediction/warehouse feature rows."""
    out = _features_with_venue_metadata(features, record)
    if out.get('weather_source') and out.get('weather_temp_f') is not None:
        return out
    out.update(_logged_outdoor_weather_snapshot(out))
    return out


def fetch_fg_projected_team_batting():
    """Fetch projected team OPS from FG batter projections (ATC DC).

    Aggregates individual batter projections by team to get a PA-weighted
    projected OPS. Used as the regression baseline for opponent quality
    so that early-season stats regress toward talent, not league average.
    """
    cached, age = _load_streaming_cache('fg_team_batting_proj.json')
    if cached is not None:
        print(f"  Using cached FG projected team batting ({age:.1f}h old)")
        return cached

    print("  Fetching FG projected team batting (ATC DC)...")
    url = "https://www.fangraphs.com/api/projections"
    params = {'type': 'ratcdc', 'stats': 'bat', 'pos': 'all', 'team': '0', 'players': '0'}
    resp = requests.get(url, params=params, headers=HEADERS, timeout=30)
    resp.raise_for_status()
    data = resp.json()

    from collections import defaultdict
    teams = defaultdict(lambda: {'pa': 0, 'obp_x_pa': 0, 'slg_x_pa': 0})
    for p in data:
        team = p.get('Team', '')
        pa = p.get('PA', 0)
        if not team or pa < 50:
            continue
        obp = p.get('OBP', 0) or 0
        slg = p.get('SLG', 0) or 0
        if isinstance(obp, str):
            obp = float(obp)
        if isinstance(slg, str):
            slg = float(slg)
        team = FG_TEAM_TO_ESPN.get(team, team)
        t = teams[team]
        t['pa'] += pa
        t['obp_x_pa'] += obp * pa
        t['slg_x_pa'] += slg * pa

    result = {}
    for team, t in teams.items():
        if t['pa'] < 100:
            continue
        obp = t['obp_x_pa'] / t['pa']
        slg = t['slg_x_pa'] / t['pa']
        result[team] = round(obp + slg, 3)

    print(f"    {len(result)} teams with projected OPS")
    _save_streaming_cache('fg_team_batting_proj.json', result)
    return result


def fetch_fg_pitcher_projections():
    """Fetch FanGraphs RoS pitcher projections with component stats."""
    print("  Fetching FG pitcher projections (component stats)...")
    url = "https://www.fangraphs.com/api/projections"
    params = {
        'type': 'ratcdc', 'stats': 'pit', 'pos': 'sp',
        'team': 0, 'players': 0, 'lg': 'all',
    }
    resp = requests.get(url, params=params, headers=HEADERS, timeout=30)
    resp.raise_for_status()
    data = resp.json()

    projections = {}
    for p in data:
        name = p.get('PlayerName', '')
        team = p.get('Team', '')
        team = FG_TEAM_TO_ESPN.get(team, team)
        gs = p.get('GS', 0) or 0
        if gs < 1:
            continue
        key = f"{normalize_name(name)}|{team}"
        projections[key] = {
            'name': name, 'team': team, 'fg_id': str(p.get('playerid', '')),
            'mlb_id': p.get('xMLBAMID'),
            'GS': gs, 'IP': p.get('IP', 0) or 0,
            'H': p.get('H', 0) or 0, 'ER': p.get('ER', 0) or 0,
            'BB': p.get('BB', 0) or 0, 'SO': p.get('SO', 0) or 0,
            'W': p.get('W', 0) or 0, 'L': p.get('L', 0) or 0,
            'ERA': p.get('ERA', 0) or 0, 'WHIP': p.get('WHIP', 0) or 0,
            'K9': p.get('K/9', 0) or 0, 'BB9': p.get('BB/9', 0) or 0,
        }
    print(f"    {len(projections)} SP projections loaded")
    return projections


def fetch_fg_recent_form():
    """Fetch FanGraphs last-14-days pitcher stats for trend analysis."""
    print("  Fetching FG recent form (last 14 days)...")
    url = "https://www.fangraphs.com/api/leaders/major-league/data"
    params = {
        'pos': 'sp', 'stats': 'pit', 'lg': 'all', 'qual': 0,
        'season': date.today().year, 'month': 3,  # month=3 = last 14 days
        'season1': date.today().year, 'ind': 0, 'team': '',
        'pageitems': 500, 'type': 8, 'sortcol': 15, 'sortdir': 'desc',
    }
    resp = requests.get(url, params=params, headers=HEADERS, timeout=30)
    resp.raise_for_status()
    data = resp.json().get('data', [])

    recent = {}
    for p in data:
        raw_name = p.get('Name', '') or p.get('PlayerName', '')
        name_match = re.search(r'>([^<]+)<', raw_name)
        name = name_match.group(1) if name_match else raw_name
        raw_team = p.get('Team', '')
        team_match = re.search(r'>([A-Z]+)<', str(raw_team))
        team = team_match.group(1) if team_match else raw_team
        team = FG_TEAM_TO_ESPN.get(team, team)
        ip = p.get('IP', 0) or 0
        if ip < 3:
            continue
        key = f"{normalize_name(name)}|{team}"
        recent[key] = {
            'IP': ip,
            'GS': p.get('GS') or p.get('G') or None,
            'ERA': p.get('ERA', 0) or 0,
            'WHIP': p.get('WHIP', 0) or 0,
            'K9': p.get('K/9', 0) or 0,
        }
    print(f"    {len(recent)} pitchers with recent data")
    return recent


def fetch_weekly_schedule(start_date, end_date):
    """Fetch probable pitchers from MLB StatsAPI for the week."""
    print(f"  Fetching MLB schedule: {start_date} to {end_date}...")
    url = "https://statsapi.mlb.com/api/v1/schedule"
    params = {
        'sportId': 1,
        'startDate': start_date,
        'endDate': end_date,
        'hydrate': 'probablePitcher(note)',
    }
    resp = requests.get(url, params=params, timeout=30)
    resp.raise_for_status()
    data = resp.json()

    games = []
    for date_entry in data.get('dates', []):
        game_date = date_entry['date']
        day_label = datetime.strptime(game_date, '%Y-%m-%d').strftime('%a')
        for game in date_entry.get('games', []):
            if game.get('gameType') != 'R':
                continue
            home = game['teams']['home']
            away = game['teams']['away']
            home_team = MLB_TEAM_TO_ABBR.get(home['team']['id'], '')
            away_team = MLB_TEAM_TO_ABBR.get(away['team']['id'], '')

            home_pp = home.get('probablePitcher')
            away_pp = away.get('probablePitcher')

            venue = game.get('venue') or {}
            venue_location = venue.get('location') or {}
            venue_meta = _mlb_venue_metadata(home_team, venue.get('name'))
            # MLB schedule data is already fetched for probables. Capture only
            # pregame-safe metadata here; outdoor weather/roof status remain
            # null until a reliable weather/roof source is wired.
            base = {
                'date': game_date, 'day': day_label,
                'game_time': game.get('gameDate', ''),
                'game_datetime': game.get('gameDate', ''),
                'game_pk': game.get('gamePk'),
                'venue_id': venue.get('id'),
                'venue_name': venue.get('name') or venue_meta.get('venue_name'),
                'venue_lat': venue_location.get('latitude') or venue_meta.get('venue_lat'),
                'venue_lon': venue_location.get('longitude') or venue_meta.get('venue_lon'),
                'roof_type': venue.get('roofType') or venue.get('roof_type') or venue_meta.get('roof_type'),
                'roof_status': None,
                'is_indoor_or_dome': venue_meta.get('is_indoor_or_dome'),
            }

            if home_pp:
                games.append({
                    **base,
                    'pitcher_name': home_pp.get('fullName', ''),
                    'pitcher_mlb_id': home_pp['id'],
                    'pitcher_hand': (home_pp.get('pitchHand') or {}).get('code'),
                    'pitcher_team': home_team,
                    'opponent': away_team,
                    'home_away': 'H',
                    'probable_source': 'mlb',
                })
            else:
                games.append({**base, 'pitcher_name': None, 'pitcher_team': home_team, 'opponent': away_team, 'home_away': 'H', 'probable_source': None})

            if away_pp:
                games.append({
                    **base,
                    'pitcher_name': away_pp.get('fullName', ''),
                    'pitcher_mlb_id': away_pp['id'],
                    'pitcher_hand': (away_pp.get('pitchHand') or {}).get('code'),
                    'pitcher_team': away_team,
                    'opponent': home_team,
                    'home_away': 'A',
                    'probable_source': 'mlb',
                })
            else:
                games.append({**base, 'pitcher_name': None, 'pitcher_team': away_team, 'opponent': home_team, 'home_away': 'A', 'probable_source': None})

    print(f"    {len(games)} pitcher slots across {len(data.get('dates', []))} days")
    return games


# ESPN team abbrev -> our canonical MLB_TEAM_TO_ABBR abbrev
_ESPN_ABBR_FIX = {
    'ARI': 'AZ',
    'CHW': 'CWS',
    'WSH': 'WSH',
}


def fetch_espn_probables(start_date, end_date):
    """Fetch probable pitchers from ESPN's public scoreboard.

    ESPN often announces probables before MLB Stats API. Used as a supplement
    to resolve TBD slots. Returns dict keyed by (date_iso, team_abbr) -> pitcher_name.
    """
    print(f"  Fetching ESPN probables: {start_date} to {end_date}...")
    start = date.fromisoformat(start_date)
    end = date.fromisoformat(end_date)
    out = {}
    days = (end - start).days + 1
    for i in range(days):
        d = start + timedelta(days=i)
        yyyymmdd = d.strftime('%Y%m%d')
        url = f"https://site.api.espn.com/apis/site/v2/sports/baseball/mlb/scoreboard?dates={yyyymmdd}"
        try:
            resp = requests.get(url, headers={'User-Agent': 'Mozilla/5.0'}, timeout=15)
            resp.raise_for_status()
            data = resp.json()
        except Exception as e:
            print(f"    {d.isoformat()}: ESPN fetch failed ({e})")
            continue
        for ev in data.get('events', []):
            for comp in ev.get('competitions', []):
                for c in comp.get('competitors', []):
                    team = c.get('team', {}).get('abbreviation', '')
                    team = _ESPN_ABBR_FIX.get(team, team)
                    probs = c.get('probables', [])
                    if not probs:
                        continue
                    nm = probs[0].get('athlete', {}).get('displayName') or probs[0].get('displayName', '')
                    if team and nm:
                        out[(d.isoformat(), team)] = nm
    print(f"    {len(out)} ESPN probable assignments")
    return out


def _ip_to_float(ip):
    """Convert MLB '5.2' style innings (5 and 2/3) to float 5.667."""
    if ip is None or ip == '':
        return 0.0
    s = str(ip)
    if '.' in s:
        whole, frac = s.split('.')
        try:
            return int(whole) + int(frac) / 3.0
        except ValueError:
            return 0.0
    try:
        return float(s)
    except ValueError:
        return 0.0


def fetch_completed_starts_for_date(date_iso, verbose=True):
    """Pull all finished SP starts on a given date from MLB Stats API boxscores.

    Returns dict {normalized_name: {'IP','ER','BB','K','H','decision','team'}}.
    Used both for blending today's lines into FG L14D and for joining past
    predictions with outcomes for the learning engine.
    """
    if verbose:
        print(f"  Fetching completed starts for {date_iso}...")
    url = (f"https://statsapi.mlb.com/api/v1/schedule?sportId=1"
           f"&date={date_iso}&hydrate=decisions")
    try:
        resp = requests.get(url, timeout=20)
        resp.raise_for_status()
        data = resp.json()
    except Exception as e:
        if verbose:
            print(f"    Schedule fetch failed: {e}")
        return {}

    final_game_pks = []
    decisions_by_pk = {}  # pk -> {'W': name, 'L': name}
    for dt in data.get('dates', []):
        for g in dt.get('games', []):
            if g.get('status', {}).get('abstractGameState') == 'Final':
                pk = g.get('gamePk')
                final_game_pks.append(pk)
                dec = g.get('decisions', {}) or {}
                decisions_by_pk[pk] = {
                    'W': (dec.get('winner') or {}).get('fullName'),
                    'L': (dec.get('loser') or {}).get('fullName'),
                }

    if not final_game_pks:
        if verbose:
            print(f"    0 final games on {date_iso}")
        return {}

    def fetch_box(pk):
        try:
            r = requests.get(
                f"https://statsapi.mlb.com/api/v1/game/{pk}/boxscore",
                timeout=15,
            )
            r.raise_for_status()
            return pk, r.json()
        except Exception:
            return pk, None

    lines = {}
    with ThreadPoolExecutor(max_workers=8) as ex:
        for pk, box in ex.map(fetch_box, final_game_pks):
            if not box:
                continue
            dec = decisions_by_pk.get(pk, {})
            for side in ('home', 'away'):
                team_info = box.get('teams', {}).get(side, {})
                team_id = team_info.get('team', {}).get('id')
                team_abbr = MLB_TEAM_TO_ABBR.get(team_id, '')
                for pid, pinfo in team_info.get('players', {}).items():
                    pos = pinfo.get('position', {}).get('abbreviation')
                    stats = pinfo.get('stats', {}).get('pitching', {})
                    gs = stats.get('gamesStarted', 0)
                    if pos == 'P' and gs:
                        name = pinfo.get('person', {}).get('fullName', '')
                        if not name:
                            continue
                        decision = ''
                        if dec.get('W') == name:
                            decision = 'W'
                        elif dec.get('L') == name:
                            decision = 'L'
                        lines[normalize_name(name)] = {
                            'name': name,
                            'team': team_abbr,
                            'IP': _ip_to_float(stats.get('inningsPitched', 0)),
                            'ER': stats.get('earnedRuns', 0) or 0,
                            'BB': stats.get('baseOnBalls', 0) or 0,
                            'K': stats.get('strikeOuts', 0) or 0,
                            'H': stats.get('hits', 0) or 0,
                            'decision': decision,
                        }
    if verbose:
        print(f"    {len(lines)} starters with completed lines on {date_iso}")
    return lines


def fetch_todays_completed_starts():
    """Backward-compat alias used by the L14D blend logic."""
    return fetch_completed_starts_for_date(date.today().isoformat())


FG_RECENT_RAW_DIR = os.path.join(SCRIPT_DIR, 'streaming_cache', 'fg_recent_raw')


def save_recent_raw_snapshot(recent):
    """Persist today's raw (pre-blend) FG L14D once per day. Used next day to
    determine whether FG has caught up with today's games (so we don't
    double-count on the blend)."""
    if PREVIEW_LOCAL:
        print("    Local preview mode: skipping L14D snapshot write")
        return
    os.makedirs(FG_RECENT_RAW_DIR, exist_ok=True)
    path = os.path.join(FG_RECENT_RAW_DIR, f"{date.today().isoformat()}.json")
    if not os.path.exists(path):
        try:
            with open(path, 'w') as f:
                json.dump(recent, f)
        except Exception as e:
            print(f"    Could not save L14D snapshot: {e}")
    # GC: keep only last 14 days
    try:
        for fn in os.listdir(FG_RECENT_RAW_DIR):
            if fn.endswith('.json'):
                try:
                    d = date.fromisoformat(fn[:-5])
                    if (date.today() - d).days > 14:
                        os.remove(os.path.join(FG_RECENT_RAW_DIR, fn))
                except ValueError:
                    continue
    except FileNotFoundError:
        pass


def load_prior_day_recent_snapshot():
    """Return the most recent L14D snapshot from a PRIOR day. Used to tell if
    FG's L14D has absorbed today's starts yet."""
    if not os.path.isdir(FG_RECENT_RAW_DIR):
        return {}
    today_iso = date.today().isoformat()
    files = sorted(
        fn for fn in os.listdir(FG_RECENT_RAW_DIR)
        if fn.endswith('.json') and fn[:-5] < today_iso
    )
    if not files:
        return {}
    try:
        with open(os.path.join(FG_RECENT_RAW_DIR, files[-1])) as f:
            return json.load(f)
    except Exception:
        return {}


def blend_today_into_recent(recent_form, today_lines, baseline_recent=None):
    """Fold today's completed starts into the L14D dict so HOLD/emerging
    assessment sees them. Recent entries are keyed by 'norm|team' AND 'norm'.

    If `baseline_recent` (prior-day FG snapshot) is supplied, skip any pitcher
    whose fresh FG L14D IP has already risen by roughly today's IP — that means
    FG caught up overnight and blending would double-count.
    """
    if not today_lines:
        return recent_form
    blended = 0
    skipped_already_in_fg = 0
    for norm, line in today_lines.items():
        ip_t = line['IP']
        if ip_t <= 0:
            continue
        er_t, bb_t, h_t, k_t = line['ER'], line['BB'], line['H'], line['K']
        team = line['team']
        candidate_keys = [f"{norm}|{team}", norm]
        # Also try with any team the recent dict has for this pitcher
        for k in list(recent_form.keys()):
            if k.startswith(norm + '|'):
                candidate_keys.append(k)

        # Double-count guard: if fresh FG IP already rose by ~today's IP vs
        # yesterday's snapshot, FG has already absorbed today's line.
        if baseline_recent:
            already = False
            for key in candidate_keys:
                fresh = recent_form.get(key)
                base = baseline_recent.get(key)
                if fresh and base:
                    if (fresh.get('IP', 0) - base.get('IP', 0)) >= (ip_t * 0.7):
                        already = True
                        break
            if already:
                skipped_already_in_fg += 1
                continue

        merged = False
        for key in candidate_keys:
            if key in recent_form:
                r = recent_form[key]
                ip_prev = r.get('IP', 0) or 0
                era_prev = r.get('ERA', 0) or 0
                whip_prev = r.get('WHIP', 0) or 0
                k9_prev = r.get('K9', 0) or 0
                er_prev = era_prev * ip_prev / 9.0
                baserunners_prev = whip_prev * ip_prev
                k_prev = k9_prev * ip_prev / 9.0
                new_ip = ip_prev + ip_t
                if new_ip <= 0:
                    continue
                new_er = er_prev + er_t
                new_br = baserunners_prev + bb_t + h_t
                new_k = k_prev + k_t
                r['IP'] = new_ip
                r['GS'] = (r.get('GS') or 0) + 1
                r['ERA'] = new_er / new_ip * 9.0
                r['WHIP'] = new_br / new_ip
                r['K9'] = new_k / new_ip * 9.0
                merged = True
        if not merged:
            # First L14D entry for this pitcher (e.g., just returned from minors)
            recent_form[f"{norm}|{team}"] = {
                'IP': ip_t,
                'GS': 1,
                'ERA': (er_t / ip_t) * 9.0 if ip_t else 0.0,
                'WHIP': (bb_t + h_t) / ip_t if ip_t else 0.0,
                'K9': (k_t / ip_t) * 9.0 if ip_t else 0.0,
            }
        blended += 1
    msg = f"    Blended {blended} starts into L14D window"
    if skipped_already_in_fg:
        msg += f" (skipped {skipped_already_in_fg} already reflected in FG)"
    print(msg)
    return recent_form


def fetch_team_offense(projected_team_ops=None):
    """Fetch team batting stats from MLB StatsAPI.

    If projected_team_ops is provided, regresses toward each team's
    preseason projection instead of league average.
    """
    print("  Fetching team offense stats...")
    url = "https://statsapi.mlb.com/api/v1/teams/stats"
    params = {'stats': 'season', 'group': 'hitting', 'season': date.today().year, 'sportIds': 1}
    resp = requests.get(url, params=params, timeout=30)
    resp.raise_for_status()

    splits = resp.json()['stats'][0]['splits']
    teams = {}
    ops_values = []
    for t in splits:
        abbr = MLB_TEAM_TO_ABBR.get(t['team']['id'], '')
        if not abbr:
            continue
        s = t['stat']
        ops = float(s.get('ops', '.700'))
        pa = int(s.get('plateAppearances', 0))
        k = int(s.get('strikeOuts', 0))
        gp = int(s.get('gamesPlayed', 1))
        runs = int(s.get('runs', 0))
        k_pct = k / pa if pa > 0 else 0.20
        rpg = runs / gp if gp > 0 else 4.5
        teams[abbr] = {'ops': ops, 'pa': pa, 'k_pct': k_pct, 'rpg': rpg}
        ops_values.append(ops)

    # Compute league average OPS
    league_avg_ops = sum(ops_values) / len(ops_values) if ops_values else 0.720

    # Regress each team's actual OPS toward their preseason projection.
    # If projections not available, fall back to league average.
    proj_avg = sum(projected_team_ops.values()) / len(projected_team_ops) if projected_team_ops else league_avg_ops
    for abbr, data in teams.items():
        actual_ops = data['ops']
        team_pa = data['pa']
        # Regression target: team's own projection (captures talent), not league avg
        target = projected_team_ops.get(abbr, league_avg_ops) if projected_team_ops else league_avg_ops
        regressed = (actual_ops * team_pa + target * OPP_REGRESS_PA) / (team_pa + OPP_REGRESS_PA)
        data['ops_regressed'] = regressed
        data['ops_projected'] = target
        data['regress_pct'] = round(OPP_REGRESS_PA / (team_pa + OPP_REGRESS_PA) * 100)

    # Rank teams by REGRESSED OPS (1 = best offense)
    sorted_teams = sorted(teams.items(), key=lambda x: x[1]['ops_regressed'], reverse=True)
    for rank, (abbr, _) in enumerate(sorted_teams, 1):
        teams[abbr]['ops_rank'] = rank

    sample_pa = teams[list(teams.keys())[0]]['pa'] if teams else 0
    regress_pct = teams[list(teams.keys())[0]].get('regress_pct', 0) if teams else 0
    using_proj = "projected team talent" if projected_team_ops else "league avg"
    print(f"    {len(teams)} teams, league avg OPS: {league_avg_ops:.3f}")
    print(f"    Teams at ~{sample_pa} PA, {regress_pct}% regressed toward {using_proj}")
    return teams, league_avg_ops


def _fetch_single_team_handedness(mlb_team_id):
    """Fetch active roster for one team and compute batter handedness breakdown."""
    try:
        url = f"https://statsapi.mlb.com/api/v1/teams/{mlb_team_id}/roster"
        params = {'rosterType': 'active', 'season': date.today().year, 'hydrate': 'person'}
        resp = requests.get(url, params=params, timeout=15)
        resp.raise_for_status()
        roster = resp.json().get('roster', [])
        left = right = switch = 0
        players = {}
        for r in roster:
            pos = r.get('position', {}).get('abbreviation', '')
            if pos == 'P':
                continue
            person = r.get('person', {}) or {}
            name = person.get('fullName') or ''
            side = (person.get('batSide') or {}).get('code') or ''
            throw_side = (person.get('pitchHand') or {}).get('code') or ''
            if name:
                players[normalize_name(name)] = {
                    'name': name,
                    'mlb_id': person.get('id'),
                    'bat_side': side or None,
                    'throws': throw_side or None,
                    'position': pos,
                }
            side = side or 'R'
            if side == 'L':
                left += 1
            elif side == 'S':
                switch += 1
            else:
                right += 1
        total = left + right + switch
        if total == 0:
            return None
        return {
            'left': left, 'right': right, 'switch': switch, 'total': total,
            'left_pct': round(left / total * 100),
            'right_pct': round(right / total * 100),
            'players': players,
        }
    except Exception:
        return None


def _team_handedness_has_player_metadata(team_handedness):
    """Return True when cached handedness includes per-player bat-side data."""
    if not isinstance(team_handedness, dict):
        return False
    for data in team_handedness.values():
        players = (data or {}).get('players')
        if isinstance(players, dict) and players:
            return True
    return False


def _load_il_snapshot_for_diff(min_age_days=4, max_age_days=14):
    """Find a previous IL snapshot to use as a baseline for detecting returns.

    We want a snapshot at least `min_age_days` old (so the diff is meaningful)
    but not so old it's irrelevant. Returns dict or None.
    """
    snap_dir = os.path.join(STREAMING_CACHE_DIR, 'il_snapshots')
    if not os.path.exists(snap_dir):
        return None
    today = date.today()
    files = sorted(f for f in os.listdir(snap_dir) if f.endswith('.json'))
    candidate = None
    for f in files:
        try:
            f_date = date.fromisoformat(f.replace('.json', ''))
        except ValueError:
            continue
        age_days = (today - f_date).days
        if min_age_days <= age_days <= max_age_days:
            candidate = (f, f_date)  # Take the most recent that fits the window
    if not candidate:
        return None
    fpath = os.path.join(snap_dir, candidate[0])
    try:
        with open(fpath, 'r') as f:
            return {'date': candidate[1].isoformat(), 'data': json.load(f)}
    except Exception:
        return None


def _save_il_snapshot(il_data):
    """Persist today's IL snapshot for future diff comparisons."""
    if PREVIEW_LOCAL:
        print("    Local preview mode: skipping IL snapshot write")
        return
    snap_dir = os.path.join(STREAMING_CACHE_DIR, 'il_snapshots')
    os.makedirs(snap_dir, exist_ok=True)
    today = date.today().isoformat()
    fpath = os.path.join(snap_dir, f"{today}.json")
    with open(fpath, 'w') as f:
        json.dump(il_data, f, indent=2)


def fetch_team_il_hitters(players_list):
    """Fetch notable hitters on the IL for each MLB team, plus recently activated stars.

    Cross-references MLB 40-man roster IL status with our RoS projections
    to identify significant bats. Also diffs against a prior snapshot to find
    players who recently came off the IL — relevant because team recent stats
    won't include them yet, so opponent OPS may understate the matchup.

    Returns: (il_by_team, returns_by_team)
    - il_by_team: {team_abbr: [{name, rank, dollars, il_type}, ...]}
    - returns_by_team: {team_abbr: [{name, rank, dollars}, ...]}
    """
    cached, age = _load_streaming_cache('team_il_hitters.json', max_age_hours=12)
    cached_returns, _ = _load_streaming_cache('team_il_returns.json', max_age_hours=12)
    if cached and cached_returns is not None:
        print(f"  Using cached IL data ({age:.1f}h old)")
        return cached, cached_returns

    print("  Fetching IL data for all 30 teams...")

    # Build lookup: normalized name -> player projection data
    hitter_lookup = {}
    for p in players_list:
        if p.get('type') == 'pitcher':
            continue
        norm = normalize_name(p['name'])
        hitter_lookup[norm] = {
            'name': p['name'], 'rank': p['rank'],
            'dollars': p['dollars'], 'team': p['team'],
        }

    il_by_team = {}  # team_abbr -> list of notable IL hitters
    # Also track ALL IL hitters by team (not just top 200) for accurate diffing
    full_il_by_team = {}  # team_abbr -> set of normalized names

    for mlb_id, abbr in MLB_TEAM_TO_ABBR.items():
        try:
            url = f"https://statsapi.mlb.com/api/v1/teams/{mlb_id}/roster"
            params = {'rosterType': '40Man', 'season': 2026, 'hydrate': 'person'}
            resp = requests.get(url, params=params, timeout=10)
            resp.raise_for_status()
            roster = resp.json().get('roster', [])

            for entry in roster:
                status = entry.get('status', {}).get('description', '')
                if 'Injured' not in status:
                    continue
                pos = entry.get('position', {}).get('abbreviation', '')
                if pos == 'P':
                    continue  # Only care about hitters
                person = entry.get('person', {})
                name = person.get('fullName', '')
                norm = normalize_name(name)

                # Track every IL hitter for diffing (even non-notable ones)
                full_il_by_team.setdefault(abbr, set()).add(norm)

                proj = hitter_lookup.get(norm)
                if proj and proj['rank'] <= 200:  # Top 200 = significant
                    il_by_team.setdefault(abbr, []).append({
                        'name': name,
                        'rank': proj['rank'],
                        'dollars': proj['dollars'],
                        'il_type': status.replace('Injured ', 'IL-'),
                    })
        except Exception:
            continue

    # Sort each team's IL list by rank (best players first)
    for abbr in il_by_team:
        il_by_team[abbr].sort(key=lambda x: x['rank'])

    total = sum(len(v) for v in il_by_team.values())
    teams_hit = len(il_by_team)
    print(f"    {total} notable hitters on IL across {teams_hit} teams")

    # Save today's snapshot (full IL list, serialized as sorted lists for JSON)
    snapshot = {abbr: sorted(names) for abbr, names in full_il_by_team.items()}
    _save_il_snapshot(snapshot)

    # Compute recently activated stars by diffing against an older snapshot
    returns_by_team = {}
    prev = _load_il_snapshot_for_diff()
    if prev:
        prev_data = {abbr: set(names) for abbr, names in prev['data'].items()}
        for abbr, prev_names in prev_data.items():
            current_names = full_il_by_team.get(abbr, set())
            activated = prev_names - current_names  # Was on IL, now not
            for norm in activated:
                proj = hitter_lookup.get(norm)
                if proj and proj['rank'] <= 200:
                    returns_by_team.setdefault(abbr, []).append({
                        'name': proj['name'],
                        'rank': proj['rank'],
                        'dollars': proj['dollars'],
                    })
        for abbr in returns_by_team:
            returns_by_team[abbr].sort(key=lambda x: x['rank'])
        ret_total = sum(len(v) for v in returns_by_team.values())
        print(f"    {ret_total} stars returned from IL since {prev['date']}")
    else:
        print(f"    No prior IL snapshot 4-14d old — first run, returns will populate next time")

    _save_streaming_cache('team_il_hitters.json', il_by_team)
    _save_streaming_cache('team_il_returns.json', returns_by_team)
    return il_by_team, returns_by_team


def fetch_team_handedness():
    """Fetch batter handedness for all 30 teams (parallelized, cached 24h)."""
    cached, age = _load_streaming_cache('team_handedness.json')
    if cached and _team_handedness_has_player_metadata(cached):
        print(f"  Using cached team handedness ({age:.1f}h old)")
        return cached
    if cached:
        print("  Cached team handedness lacks player bat-side metadata; refreshing")

    print("  Fetching team roster handedness (30 teams)...")
    results = {}
    with ThreadPoolExecutor(max_workers=10) as executor:
        futures = {}
        for abbr, mlb_id in ABBR_TO_MLB_TEAM.items():
            futures[executor.submit(_fetch_single_team_handedness, mlb_id)] = abbr
        for future in as_completed(futures):
            abbr = futures[future]
            data = future.result()
            if data:
                for player in (data.get('players') or {}).values():
                    player['team'] = abbr
                results[abbr] = data

    _save_streaming_cache('team_handedness.json', results)
    print(f"    {len(results)} teams loaded")
    return results


def _aggregate_recent_splits(splits, max_seasons=3):
    """IP-weighted aggregate of the last N seasons of splits (vs L / vs R).

    Aging vets (Scherzer at 41 vs 2018 prime Scherzer) have very different
    recent splits than career splits. Career averages mask decline. Using only
    the last 3 seasons reflects the current version of the pitcher.

    Returns ({'l': {ops, whip, k9, ip}, 'r': {...}, 'window_years': N}) or None.
    """
    by_year = {}  # year -> {'l': stat_dict, 'r': stat_dict}
    for split in splits:
        season = split.get('season')
        try:
            y = int(season) if season else None
        except (ValueError, TypeError):
            y = None
        if y is None:
            continue
        desc = split.get('split', {}).get('description', '') or ''
        st = split.get('stat', {})
        if 'Left' in desc:
            by_year.setdefault(y, {})['l'] = st
        elif 'Right' in desc:
            by_year.setdefault(y, {})['r'] = st

    if not by_year:
        return None

    target_years = sorted(by_year.keys(), reverse=True)[:max_seasons]

    def _blend(side):
        total_ip = 0.0
        wsum_ops = wsum_whip = wsum_k9 = 0.0
        for y in target_years:
            s = by_year.get(y, {}).get(side, {})
            if not s:
                continue
            ip = _ip_to_float(s.get('inningsPitched', 0))
            if ip <= 0:
                continue
            try:
                ops = float(s.get('ops', 0) or 0)
                whip = float(s.get('whip', 0) or 0)
                k9 = float(s.get('strikeoutsPer9Inn', 0) or 0)
            except (ValueError, TypeError):
                continue
            wsum_ops += ops * ip
            wsum_whip += whip * ip
            wsum_k9 += k9 * ip
            total_ip += ip
        if total_ip < 15:  # too little data — unreliable
            return None
        return {
            'ops': f'{wsum_ops / total_ip:.3f}',
            'whip': f'{wsum_whip / total_ip:.2f}',
            'k9': f'{wsum_k9 / total_ip:.2f}',
            'ip': f'{total_ip:.1f}',
        }

    out = {'l': _blend('l'), 'r': _blend('r'), 'window_years': len(target_years)}
    if not out['l'] and not out['r']:
        return None
    return out


def _fetch_single_pitcher_details(mlb_id):
    """Fetch last-3-seasons platoon splits + pitch arsenal for one pitcher.

    The MLB Stats API only returns splits one season at a time via statSplits,
    so we issue 3 calls (current year and the two prior). Aging vets'
    decline shows up here — Scherzer's 2018 dominance no longer drowns out
    his 2025 numbers.
    """
    try:
        result = {'mlb_id': mlb_id}
        url = f"https://statsapi.mlb.com/api/v1/people/{mlb_id}/stats"
        current_year = date.today().year
        seasons_to_query = [current_year, current_year - 1, current_year - 2]
        all_splits = []  # list of split dicts annotated with year

        # First call also fetches arsenal (saves one round-trip)
        first = True
        for yr in seasons_to_query:
            stats_param = 'statSplits,pitchArsenal' if first else 'statSplits'
            try:
                resp = requests.get(url, params={
                    'stats': stats_param,
                    'season': yr,
                    'group': 'pitching',
                    'sitCodes': 'vl,vr',
                }, timeout=15)
                if resp.status_code != 200:
                    first = False
                    continue
                data = resp.json()
            except Exception:
                first = False
                continue

            for stat_group in data.get('stats', []):
                type_name = stat_group.get('type', {}).get('displayName', '')
                if 'Splits' in type_name:
                    for sp in stat_group.get('splits', []):
                        # Annotate with year so the aggregator can dedupe across seasons
                        sp['season'] = sp.get('season') or str(yr)
                        all_splits.append(sp)
                elif first and 'Arsenal' in type_name:
                    pitches = []
                    fb_velo = None
                    for split in stat_group.get('splits', []):
                        st = split.get('stat', {})
                        pitch_type = st.get('type', {}).get('code', '')
                        pitch_desc = st.get('type', {}).get('description', '')
                        velo = st.get('averageSpeed')
                        pct = st.get('percentage', 0)
                        pitches.append({'code': pitch_type, 'desc': pitch_desc, 'velo': velo, 'pct': pct})
                        if pitch_type in ('FF', 'SI') and velo and (fb_velo is None or pct > 0.3):
                            fb_velo = round(velo, 1)
                    result['pitches'] = pitches
                    result['fb_velo'] = fb_velo
                    result['pitch_count'] = len(pitches)
            first = False

        # Aggregate all collected splits across the 3 seasons
        if all_splits:
            aggregated = _aggregate_recent_splits(all_splits, max_seasons=3)
            if aggregated:
                if aggregated.get('l'):
                    result['career_vs_l'] = aggregated['l']
                if aggregated.get('r'):
                    result['career_vs_r'] = aggregated['r']
                result['splits_window_years'] = aggregated.get('window_years', 3)

        return result
    except Exception:
        return {'mlb_id': mlb_id}


def _fetch_single_pitcher_hand(mlb_id):
    try:
        resp = requests.get(f"https://statsapi.mlb.com/api/v1/people/{mlb_id}", timeout=10)
        resp.raise_for_status()
        people = resp.json().get('people') or []
        if not people:
            return str(mlb_id), None
        hand = (people[0].get('pitchHand') or {}).get('code')
        return str(mlb_id), hand
    except Exception:
        return str(mlb_id), None


def fetch_pitcher_details(mlb_ids):
    """Fetch career splits + arsenal for a list of MLB pitcher IDs (parallelized, cached)."""
    cached, age = _load_streaming_cache('pitcher_details.json')
    if cached is None:
        cached = {}

    # Only fetch IDs not in cache or stale
    to_fetch = [mid for mid in mlb_ids if str(mid) not in cached]
    if to_fetch:
        print(f"  Fetching pitcher details ({len(to_fetch)} new, {len(mlb_ids) - len(to_fetch)} cached)...")
        with ThreadPoolExecutor(max_workers=10) as executor:
            futures = {executor.submit(_fetch_single_pitcher_details, mid): mid for mid in to_fetch}
            for future in as_completed(futures):
                result = future.result()
                if result:
                    cached[str(result['mlb_id'])] = result

        _save_streaming_cache('pitcher_details.json', cached)
    else:
        print(f"  Using cached pitcher details ({len(mlb_ids)} pitchers)")

    hand_missing = [mid for mid in mlb_ids if str(mid) in cached and not cached.get(str(mid), {}).get('pitcher_hand')]
    if hand_missing:
        print(f"  Fetching pitcher handedness ({len(hand_missing)} missing)...")
        with ThreadPoolExecutor(max_workers=10) as executor:
            for mid, hand in executor.map(_fetch_single_pitcher_hand, hand_missing):
                if hand:
                    cached.setdefault(str(mid), {})['pitcher_hand'] = hand
        _save_streaming_cache('pitcher_details.json', cached)

    return cached


# --- Savant Pitch Arsenal Stats ---

SAVANT_PITCH_TYPES = ['FF', 'SI', 'SL', 'CU', 'CH', 'FC', 'FS', 'ST']
SAVANT_ARSENAL_URL = 'https://baseballsavant.mlb.com/leaderboard/pitch-arsenal-stats'


def _parse_savant_csv(text):
    """Parse Savant CSV response, handling BOM and quoted name column."""
    import csv as _csv
    import io as _io
    text = text.lstrip('\ufeff')
    reader = _csv.DictReader(_io.StringIO(text))
    return list(reader)


def _safe_float(val, default=None):
    """Convert a value to float, returning default if empty/invalid.
    Handles strings, ints, floats, and None safely."""
    if val is None:
        return default
    if isinstance(val, (int, float)):
        try:
            return float(val) if val == val else default  # filter NaN
        except Exception:
            return default
    try:
        s = str(val).strip()
        return float(s) if s else default
    except (ValueError, TypeError):
        return default


def fetch_savant_pitch_arsenal():
    """Fetch pitcher and team-batter pitch arsenal stats from Savant. Cached 24h."""
    cached, age = _load_streaming_cache('savant_arsenal.json')
    if cached is not None:
        print(f"  Using cached Savant arsenal data ({age:.1f}h old)")
        return cached

    print("  Fetching Savant pitch arsenal stats (pitcher + batter)...")
    pitcher_data = {}  # {mlb_id_str: {pitch_code: {whiff, woba, rv100, usage, ba, slg, hard_hit}}}
    team_batting = {}  # {team_abbr: {pitch_code: {woba, whiff, rv100, pa}}}
    league_avgs = {}   # {pitch_code: {woba, whiff}} for benchmarking

    for pt in SAVANT_PITCH_TYPES:
        # Pitcher side
        try:
            resp = requests.get(SAVANT_ARSENAL_URL, params={
                'type': 'pitcher', 'pitchType': pt, 'year': date.today().year,
                'min': 10, 'csv': 'true'
            }, headers={'User-Agent': 'Mozilla/5.0'}, timeout=20)
            rows = _parse_savant_csv(resp.text)
            all_woba, all_whiff, all_pa = [], [], []
            for r in rows:
                pid = r.get('player_id', '').strip()
                if not pid:
                    continue
                whiff = _safe_float(r.get('whiff_percent'))
                woba = _safe_float(r.get('woba'))
                rv100 = _safe_float(r.get('run_value_per_100'))
                usage = _safe_float(r.get('pitch_usage'))
                ba = _safe_float(r.get('ba'))
                slg = _safe_float(r.get('slg'))
                hard_hit = _safe_float(r.get('hard_hit_percent'))
                pa = _safe_float(r.get('pa'), 0)
                if pid not in pitcher_data:
                    pitcher_data[pid] = {}
                pitcher_data[pid][pt] = {
                    'whiff': whiff, 'woba': woba, 'rv100': rv100,
                    'usage': usage, 'ba': ba, 'slg': slg,
                    'hard_hit': hard_hit,
                }
                if woba is not None and pa:
                    all_woba.append((woba, pa))
                    all_whiff.append((whiff or 0, pa))
                    all_pa.append(pa)
            # League average for this pitch type
            total_pa = sum(p for _, p in all_woba) if all_woba else 1
            if total_pa > 0:
                league_avgs[pt] = {
                    'woba': sum(w * p for w, p in all_woba) / total_pa,
                    'whiff': sum(w * p for w, p in all_whiff) / total_pa,
                }
        except Exception as e:
            print(f"    Warning: Savant pitcher {pt} failed: {e}")

        # Batter side
        try:
            resp = requests.get(SAVANT_ARSENAL_URL, params={
                'type': 'batter', 'pitchType': pt, 'year': date.today().year,
                'min': 5, 'csv': 'true'
            }, headers={'User-Agent': 'Mozilla/5.0'}, timeout=20)
            rows = _parse_savant_csv(resp.text)
            # Aggregate by team (PA-weighted)
            team_agg = {}  # {team: {sum_woba_pa, sum_whiff_pa, sum_rv100_pa, total_pa}}
            for r in rows:
                team = r.get('team_name_alt', '').strip()
                pa = _safe_float(r.get('pa'), 0)
                if not team or pa < 1:
                    continue
                woba = _safe_float(r.get('woba'))
                whiff = _safe_float(r.get('whiff_percent'))
                rv100 = _safe_float(r.get('run_value_per_100'))
                if team not in team_agg:
                    team_agg[team] = {'woba_pa': 0, 'whiff_pa': 0, 'rv100_pa': 0, 'pa': 0}
                a = team_agg[team]
                a['pa'] += pa
                if woba is not None:
                    a['woba_pa'] += woba * pa
                if whiff is not None:
                    a['whiff_pa'] += whiff * pa
                if rv100 is not None:
                    a['rv100_pa'] += rv100 * pa
            for team, a in team_agg.items():
                if a['pa'] < 1:
                    continue
                if team not in team_batting:
                    team_batting[team] = {}
                team_batting[team][pt] = {
                    'woba': round(a['woba_pa'] / a['pa'], 3),
                    'whiff': round(a['whiff_pa'] / a['pa'], 1),
                    'rv100': round(a['rv100_pa'] / a['pa'], 2),
                    'pa': int(a['pa']),
                }
        except Exception as e:
            print(f"    Warning: Savant batter {pt} failed: {e}")

    # Map team name variations (Savant uses some different abbreviations)
    team_name_map = {'ARI': 'AZ', 'OAK': 'ATH', 'WSN': 'WSH'}
    for old, new in team_name_map.items():
        if old in team_batting and new not in team_batting:
            team_batting[new] = team_batting.pop(old)

    result = {
        'pitcher': pitcher_data,
        'team_batting': team_batting,
        'league_avgs': league_avgs,
    }
    n_pitchers = len(pitcher_data)
    n_teams = len(team_batting)
    print(f"    {n_pitchers} pitchers, {n_teams} teams across {len(SAVANT_PITCH_TYPES)} pitch types")
    _save_streaming_cache('savant_arsenal.json', result)
    return result


def fetch_savant_advanced_pitcher_stats():
    """Pull Savant 'expected statistics' (xERA, xWOBA, xBA, xSLG, barrel%, hard-hit%)
    plus whiff/CSW/chase rate per pitcher. Returns dict keyed by mlb_id (string).
    Cached 24h. Free, public, no auth.
    """
    cached, age = _load_streaming_cache('savant_advanced.json')
    if cached is not None:
        print(f"  Using cached Savant advanced stats ({age:.1f}h old)")
        return cached

    print("  Fetching Savant advanced pitcher stats (xERA, xWOBA, barrel%, etc)...")
    out = {}
    year = date.today().year

    # Endpoint 1: expected statistics (xERA, xWOBA, xBA, xSLG)
    try:
        resp = requests.get(
            'https://baseballsavant.mlb.com/leaderboard/expected_statistics',
            params={'type': 'pitcher', 'year': year, 'min': 'q', 'csv': 'true',
                    'pitchHand': '', 'team': '', 'filter': ''},
            headers={'User-Agent': 'Mozilla/5.0'}, timeout=30,
        )
        for r in _parse_savant_csv(resp.text):
            pid = (r.get('player_id') or '').strip()
            if not pid:
                continue
            out.setdefault(pid, {})
            out[pid].update({
                'xera': _safe_float(r.get('xera')),
                'xwoba': _safe_float(r.get('xwoba')),
                'xba': _safe_float(r.get('xba')),
                'xslg': _safe_float(r.get('xslg')),
                'woba_diff': _safe_float(r.get('woba_minus_xwoba_diff')),
            })
    except Exception as e:
        print(f"    expected_statistics failed: {e}")

    # Endpoint 2: pitcher percentile / quality stats (barrel%, hard-hit%, whiff%, chase%)
    try:
        resp = requests.get(
            'https://baseballsavant.mlb.com/leaderboard/custom',
            params={
                'year': year, 'type': 'pitcher', 'min': 'q', 'selections':
                'p_total_pa,barrel_batted_rate,hard_hit_percent,whiff_percent,k_percent,bb_percent,'
                'chase_percent,oz_swing_percent,xba,xera,xwoba,p_ground_ball,p_fly_ball,p_line_drive',
                'csv': 'true',
            },
            headers={'User-Agent': 'Mozilla/5.0'}, timeout=30,
        )
        for r in _parse_savant_csv(resp.text):
            pid = (r.get('player_id') or '').strip()
            if not pid:
                continue
            out.setdefault(pid, {})
            out[pid].update({
                'barrel_pct': _safe_float(r.get('barrel_batted_rate')),
                'hard_hit_pct': _safe_float(r.get('hard_hit_percent')),
                'whiff_pct': _safe_float(r.get('whiff_percent')),
                'k_pct': _safe_float(r.get('k_percent')),
                'bb_pct': _safe_float(r.get('bb_percent')),
                'chase_pct': _safe_float(r.get('chase_percent')),
                'gb_pct': _safe_float(r.get('p_ground_ball')),
                'fb_pct': _safe_float(r.get('p_fly_ball')),
                'ld_pct': _safe_float(r.get('p_line_drive')),
            })
    except Exception as e:
        print(f"    custom leaderboard failed: {e}")

    print(f"    {len(out)} pitchers with advanced Statcast stats")
    _save_streaming_cache('savant_advanced.json', out)
    return out


def fetch_fg_pitching_plus():
    """Pull FanGraphs Stuff+, Location+, Pitching+ (their pitch-quality models)
    for all SPs. Cached 24h. Returns dict keyed by 'normalized_name|team'.
    """
    cached, age = _load_streaming_cache('fg_pitching_plus.json')
    if cached is not None:
        print(f"  Using cached FG Pitching+ data ({age:.1f}h old)")
        return cached

    print("  Fetching FG Pitching+ / Stuff+ / Location+ ...")
    out = {}
    try:
        resp = requests.get(
            'https://www.fangraphs.com/api/leaders/major-league/data',
            params={
                'pos': 'sp', 'stats': 'pit', 'lg': 'all', 'qual': 0,
                'season': date.today().year, 'season1': date.today().year,
                'ind': 0, 'team': '', 'pageitems': 500, 'type': 36,
                # type=36 returns pitching+ models
            },
            headers=HEADERS, timeout=30,
        )
        data = resp.json().get('data', [])
        for p in data:
            try:
                raw_name = p.get('Name') or p.get('PlayerName', '')
                if not isinstance(raw_name, str):
                    continue
                m = re.search(r'>([^<]+)<', raw_name)
                name = m.group(1) if m else raw_name
                raw_team = p.get('Team', '')
                team_str = str(raw_team) if raw_team is not None else ''
                tm = re.search(r'>([A-Z]+)<', team_str)
                team = tm.group(1) if tm else (team_str if isinstance(raw_team, str) else '')
                if isinstance(team, str):
                    team = FG_TEAM_TO_ESPN.get(team, team)
                else:
                    team = ''
                key = f"{normalize_name(name)}|{team}"
            except Exception:
                continue
            out[key] = {
                'stuff_plus': _safe_float(p.get('Stuff+')),
                'location_plus': _safe_float(p.get('Location+')),
                'pitching_plus': _safe_float(p.get('Pitching+')),
                'fip': _safe_float(p.get('FIP')),
                'xfip': _safe_float(p.get('xFIP')),
                'siera': _safe_float(p.get('SIERA')),
                'k_pct': _safe_float(p.get('K%') or p.get('K_pct')),
                'bb_pct': _safe_float(p.get('BB%') or p.get('BB_pct')),
                'swstr_pct': _safe_float(p.get('SwStr%') or p.get('SwStr_pct')),
            }
    except Exception as e:
        print(f"    FG Pitching+ fetch failed: {e}")

    print(f"    {len(out)} pitchers with Pitching+ data")
    _save_streaming_cache('fg_pitching_plus.json', out)
    return out


def fetch_team_bullpens():
    """Team bullpen quality (ERA, FIP, WHIP) — affects W/L probability.
    Cached 12h. Returns dict {team_abbr: {era, fip, whip, k9, bb9}}.
    """
    cached, age = _load_streaming_cache('team_bullpens.json', max_age_hours=12)
    if cached is not None:
        print(f"  Using cached team bullpens ({age:.1f}h old)")
        return cached

    print("  Fetching team bullpen stats...")
    out = {}
    try:
        url = 'https://statsapi.mlb.com/api/v1/teams/stats'
        params = {
            'season': date.today().year, 'sportIds': 1, 'group': 'pitching',
            'stats': 'season', 'gameType': 'R',
        }
        resp = requests.get(url, params=params, timeout=20)
        data = resp.json()
        # Per-team season pitching stats (combined SP+RP). To isolate the bullpen
        # we'd need to subtract starters. As a proxy we use overall team pitching
        # which still correlates with bullpen quality.
        for split in data.get('stats', []):
            for sp in split.get('splits', []):
                team = sp.get('team', {})
                team_id = team.get('id')
                team_abbr = MLB_TEAM_TO_ABBR.get(team_id)
                if not team_abbr:
                    continue
                stat = sp.get('stat', {})
                out[team_abbr] = {
                    'era': _safe_float(stat.get('era')),
                    'whip': _safe_float(stat.get('whip')),
                    'k9': _safe_float(stat.get('strikeoutsPer9Inn')),
                    'bb9': _safe_float(stat.get('walksPer9Inn')),
                }
    except Exception as e:
        print(f"    team bullpens fetch failed: {e}")

    print(f"    {len(out)} teams with bullpen stats")
    _save_streaming_cache('team_bullpens.json', out)
    return out


def _safe_int(value, default=None):
    try:
        if value is None or value == '':
            return default
        if isinstance(value, str):
            value = value.strip()
            if not value:
                return default
        return int(float(value))
    except Exception:
        return default


def _pitch_count_from_stat(stat):
    """Return exact pitch count only when MLB supplies one; never estimate."""
    if not isinstance(stat, dict):
        return None
    for key in ('pitchesThrown', 'numberOfPitches', 'pitchCount', 'pitches'):
        val = _safe_int(stat.get(key))
        if val is not None and val > 0:
            return val
    return None


def _workload_ip_to_float(value):
    """Parse workload IP from either decimal JSON outcomes or MLB 5.2 notation."""
    if value is None or value == '':
        return None
    if isinstance(value, (int, float)):
        return _safe_float(value)
    raw = str(value).strip()
    if '.' in raw:
        whole, frac = raw.split('.', 1)
        if len(frac) == 1 and frac in ('0', '1', '2'):
            return _ip_to_float(raw)
    return _safe_float(raw)


def _game_log_start_date(split):
    for key in ('date', 'gameDate'):
        raw = split.get(key)
        if raw:
            return str(raw)[:10]
    game = split.get('game') or {}
    for key in ('gameDate', 'officialDate'):
        raw = game.get(key)
        if raw:
            return str(raw)[:10]
    return None


def _add_workload_start(workload, pitcher_norm, start):
    if not pitcher_norm or not start.get('date'):
        return
    starts = workload.setdefault(pitcher_norm, {'starts': []})['starts']
    existing = next((s for s in starts if s.get('date') == start.get('date')), None)
    if existing:
        # Prefer records with exact pitch counts, then keep any missing IP/source
        # detail from the newer candidate.
        if existing.get('pitch_count') is None and start.get('pitch_count') is not None:
            existing['pitch_count'] = start.get('pitch_count')
            existing['pitch_count_source'] = start.get('pitch_count_source')
        if existing.get('ip') is None and start.get('ip') is not None:
            existing['ip'] = start.get('ip')
        sources = {existing.get('source'), start.get('source')}
        existing['source'] = '+'.join(sorted(s for s in sources if s))
        return
    starts.append(start)


def _fetch_mlb_pitcher_workload_starts(pitcher_ids):
    """Fetch cached MLB game-log starts for exact pitch count/IP workload fields."""
    pitcher_ids = sorted({str(pid) for pid in (pitcher_ids or []) if pid})
    if not pitcher_ids:
        return {}

    cached, age = _load_streaming_cache(PITCHER_WORKLOAD_HISTORY_CACHE_FILE, max_age_hours=12)
    cache = cached if isinstance(cached, dict) else {}
    current_year = date.today().year
    missing = [pid for pid in pitcher_ids if pid not in cache]
    if missing:
        print(f"  Fetching MLB workload game logs ({len(missing)} new, {len(pitcher_ids) - len(missing)} cached)...")

    def fetch_one(pid):
        starts = []
        try:
            resp = requests.get(
                f"https://statsapi.mlb.com/api/v1/people/{pid}/stats",
                params={'stats': 'gameLog', 'group': 'pitching', 'season': current_year},
                timeout=15,
            )
            resp.raise_for_status()
            data = resp.json()
        except Exception:
            return pid, starts

        for group in data.get('stats', []):
            for split in group.get('splits', []):
                stat = split.get('stat') or {}
                if _safe_int(stat.get('gamesStarted'), 0) <= 0:
                    continue
                start_date = _game_log_start_date(split)
                if not start_date:
                    continue
                ip = _workload_ip_to_float(stat.get('inningsPitched'))
                starts.append({
                    'date': start_date,
                    'ip': round(ip, 2) if ip is not None else None,
                    'pitch_count': _pitch_count_from_stat(stat),
                    'pitch_count_source': 'mlb_game_log' if _pitch_count_from_stat(stat) is not None else None,
                    'source': 'mlb_game_log',
                })
        starts.sort(key=lambda s: s.get('date') or '')
        return pid, starts

    if missing:
        with ThreadPoolExecutor(max_workers=8) as ex:
            for pid, starts in ex.map(fetch_one, missing):
                cache[pid] = {
                    'fetched_at': datetime.utcnow().isoformat(timespec='seconds') + 'Z',
                    'season': current_year,
                    'starts': starts,
                }
        _save_streaming_cache(PITCHER_WORKLOAD_HISTORY_CACHE_FILE, cache)
    elif age is not None:
        print(f"  Using cached MLB workload game logs ({age:.1f}h old)")
    return cache


def _workload_features_for_game(workload_entry, target_game_date):
    starts = list((workload_entry or {}).get('starts') or [])
    try:
        target_dt = date.fromisoformat(str(target_game_date)[:10])
    except Exception:
        return {
            'days_rest': None,
            'last_pitch_count': None,
            'last_start_ip': None,
            'last_start_pitch_count': None,
            'avg_ip_last_3_starts': None,
            'avg_pitch_count_last_3_starts': None,
            'max_pitch_count_last_5_starts': None,
            'season_avg_ip_per_start': None,
            'season_avg_pitches_per_start': None,
            'short_rest_flag': None,
            'extra_rest_flag': None,
            'workload_risk_score': None,
            'workload_note': 'missing target game date',
        }

    prior = [s for s in starts if s.get('date') and s.get('date') < target_dt.isoformat()]
    prior.sort(key=lambda s: s.get('date') or '')
    if not prior:
        return {
            'days_rest': None,
            'last_pitch_count': None,
            'last_start_ip': None,
            'last_start_pitch_count': None,
            'avg_ip_last_3_starts': None,
            'avg_pitch_count_last_3_starts': None,
            'max_pitch_count_last_5_starts': None,
            'season_avg_ip_per_start': None,
            'season_avg_pitches_per_start': None,
            'short_rest_flag': None,
            'extra_rest_flag': None,
            'workload_risk_score': 0.35,
            'workload_note': 'No prior starts found before game date.',
        }

    last = prior[-1]
    last_date = date.fromisoformat(last['date'])
    days_rest = (target_dt - last_date).days
    last3 = prior[-3:]
    last5 = prior[-5:]
    season_starts = [s for s in prior if str(s.get('date', '')).startswith(str(target_dt.year))]

    def avg(values):
        vals = [v for v in values if v is not None]
        return round(sum(vals) / len(vals), 2) if vals else None

    last_ip = _safe_float(last.get('ip'))
    last_pitch_count = _safe_int(last.get('pitch_count'))
    avg_ip3 = avg([_safe_float(s.get('ip')) for s in last3])
    pc3_values = [_safe_int(s.get('pitch_count')) for s in last3]
    pc5_values = [_safe_int(s.get('pitch_count')) for s in last5]
    season_ip_avg = avg([_safe_float(s.get('ip')) for s in season_starts])
    season_pc_avg = avg([_safe_int(s.get('pitch_count')) for s in season_starts])

    risk = 0.0
    notes = []
    if days_rest <= 4:
        risk += 0.35
        notes.append(f'short rest ({days_rest} days)')
    elif days_rest >= 7:
        risk += 0.08
        notes.append(f'extra rest ({days_rest} days)')
    else:
        notes.append(f'{days_rest} days rest')
    if last_ip is not None and last_ip < 4.0:
        risk += 0.18
        notes.append(f'last start {last_ip:.1f} IP')
    if avg_ip3 is not None and avg_ip3 < 4.5:
        risk += 0.16
        notes.append(f'avg {avg_ip3:.1f} IP last 3')
    if last_pitch_count is not None and last_pitch_count >= 105:
        risk += 0.18
        notes.append(f'{last_pitch_count} pitches last start')
    if not any(v is not None for v in pc3_values):
        notes.append('exact pitch counts unavailable')

    ip_text = f"{last_ip:.1f} IP" if last_ip is not None else "IP unavailable"
    pc_text = f", {last_pitch_count} pitches" if last_pitch_count is not None else ", exact pitch count unavailable"
    note = f"Last start {last['date']}: {ip_text}{pc_text}; " + '; '.join(notes[:3])
    return {
        'days_rest': days_rest,
        'last_pitch_count': last_pitch_count,
        'last_start_ip': round(last_ip, 2) if last_ip is not None else None,
        'last_start_pitch_count': last_pitch_count,
        'avg_ip_last_3_starts': avg_ip3,
        'avg_pitch_count_last_3_starts': avg(pc3_values),
        'max_pitch_count_last_5_starts': max([v for v in pc5_values if v is not None], default=None),
        'season_avg_ip_per_start': season_ip_avg,
        'season_avg_pitches_per_start': season_pc_avg,
        'short_rest_flag': days_rest <= 4,
        'extra_rest_flag': days_rest >= 7,
        'workload_risk_score': round(min(max(risk, 0.0), 1.0), 2),
        'workload_note': note[:180],
    }


def compute_pitcher_workload(predictions_dir, outcomes_log, pitcher_ids_by_name=None):
    """Build pregame-safe workload history from cached outcomes plus MLB game logs.

    Returns dict keyed by normalized pitcher name with prior starts only; callers
    resolve features against each target game date to avoid future leakage.
    """
    workload = {}

    if os.path.exists(outcomes_log):
        try:
            with open(outcomes_log) as f:
                for line in f:
                    try:
                        s = json.loads(line)
                    except Exception:
                        continue
                    if s.get('no_start'):
                        continue
                    pname = normalize_name(s.get('name', ''))
                    sdate = s.get('date')
                    if not pname or not sdate:
                        continue
                    line_data = s.get('actual_line') or {}
                    if isinstance(line_data, str):
                        try:
                            line_data = json.loads(line_data)
                        except Exception:
                            line_data = {}
                    pitch_count = _pitch_count_from_stat(line_data)
                    _add_workload_start(workload, pname, {
                        'date': str(sdate)[:10],
                        'ip': _workload_ip_to_float(line_data.get('IP')),
                        'pitch_count': pitch_count,
                        'pitch_count_source': 'outcome_actual_line' if pitch_count is not None else None,
                        'source': 'predictions_outcomes',
                    })
        except Exception:
            pass

    ids_by_name = pitcher_ids_by_name or {}
    game_logs = _fetch_mlb_pitcher_workload_starts(ids_by_name.values())
    for pname, pid in ids_by_name.items():
        entry = game_logs.get(str(pid)) or {}
        for start in entry.get('starts') or []:
            _add_workload_start(workload, pname, dict(start))

    for entry in workload.values():
        entry['starts'].sort(key=lambda s: s.get('date') or '')
    return workload


def augment_workload_pitcher_ids(pitcher_ids_by_name, fg_proj, espn_probables=None,
                                 roster_map=None, espn_matches=None):
    """Include ESPN/inferred candidates in workload game-log coverage.

    MLB schedule probables already carry MLBAM IDs. ESPN-only and roster-inferred
    candidates can otherwise miss game-log workload checks, which lets a stale
    probable survive if the pitcher appears only once in the window.
    """
    ids = dict(pitcher_ids_by_name or {})
    target_norms = {
        normalize_name(name)
        for name in (espn_probables or {}).values()
        if name
    }

    if roster_map and espn_matches:
        espn_matches_norm = {
            normalize_name(name): info
            for name, info in (espn_matches or {}).items()
        }
        for proj in (fg_proj or {}).values():
            name = proj.get('name') or ''
            norm = normalize_name(name)
            match_entry = (espn_matches or {}).get(name) or espn_matches_norm.get(norm)
            if not match_entry:
                continue
            roster_info = (roster_map or {}).get(match_entry.get('espn_id'))
            if roster_info and roster_info.get('team_id') == ESPN_TEAM_ID and _safe_float(proj.get('GS')) >= 5:
                target_norms.add(norm)

    for proj in (fg_proj or {}).values():
        name = proj.get('name') or ''
        norm = normalize_name(name)
        mlb_id = proj.get('mlb_id')
        if norm and mlb_id and norm in target_norms:
            ids.setdefault(norm, mlb_id)
    return ids


# =============================================================================
# DATA PROCESSING
# =============================================================================

def parse_fg_positions(pos_str):
    if not pos_str:
        return ['DH']
    positions = [p.strip() for p in pos_str.split('/')]
    mapped = []
    for p in positions:
        if p in ('LF', 'CF', 'RF'):
            if 'OF' not in mapped:
                mapped.append('OF')
        else:
            mapped.append(p)
    return mapped if mapped else ['DH']


def pick_display_pos(positions):
    for premium in PREMIUM_POS_ORDER:
        if premium in positions:
            return premium
    return positions[0] if positions else 'DH'


def process_fg_batters(raw_data):
    rows = []
    for p in raw_data:
        name = p.get('PlayerName', 'Unknown')
        fg_team = p.get('Team', '') or ''
        team = FG_TEAM_TO_ESPN.get(fg_team, fg_team)
        positions = parse_fg_positions(p.get('POS', 'DH'))
        rows.append({
            'name': name, 'team': team, 'positions': positions,
            'primary_pos': pick_display_pos(positions),
            'dollars': round(p.get('Dollars', 0), 1),
            'rpts': round(p.get('rPTS', 0), 1),
            'type': 'hitter', 'fg_id': str(p.get('playerid', '')),
        })
    return pd.DataFrame(rows)


def process_fg_pitchers(raw_data):
    rows = []
    for p in raw_data:
        name = p.get('PlayerName', 'Unknown')
        fg_team = p.get('Team', '') or ''
        team = FG_TEAM_TO_ESPN.get(fg_team, fg_team)
        role = p.get('POS', 'SP')
        if role not in ('SP', 'RP'):
            role = 'SP'
        rows.append({
            'name': name, 'team': team, 'positions': ['P'],
            'primary_pos': 'P', 'pitcher_role': role,
            'dollars': round(p.get('Dollars', 0), 1),
            'rpts': round(p.get('rPTS', 0), 1),
            'type': 'pitcher', 'fg_id': str(p.get('playerid', '')),
        })
    return pd.DataFrame(rows)


def combine_ohtani(batters_df, pitchers_df):
    ohtani_bat = batters_df[batters_df['name'].str.contains('Ohtani', case=False, na=False)]
    ohtani_pit = pitchers_df[pitchers_df['name'].str.contains('Ohtani', case=False, na=False)]
    if len(ohtani_bat) > 0 and len(ohtani_pit) > 0:
        bat_dollars = ohtani_bat.iloc[0]['dollars']
        pit_dollars = ohtani_pit.iloc[0]['dollars']
        combined_dollars = bat_dollars + pit_dollars
        combined_rpts = ohtani_bat.iloc[0]['rpts'] + ohtani_pit.iloc[0]['rpts']
        print(f"  Ohtani: ${bat_dollars:.1f} (bat) + ${pit_dollars:.1f} (pit) = ${combined_dollars:.1f}")
        idx = ohtani_bat.index[0]
        batters_df.at[idx, 'dollars'] = combined_dollars
        batters_df.at[idx, 'rpts'] = combined_rpts
        batters_df.at[idx, 'positions'] = ['DH', 'P']
        batters_df.at[idx, 'type'] = 'two-way'
        batters_df.at[idx, 'pitcher_role'] = 'SP'
        pitchers_df = pitchers_df[~pitchers_df['name'].str.contains('Ohtani', case=False, na=False)]
    return batters_df, pitchers_df


def create_rankings(batters_df, pitchers_df):
    batters_df, pitchers_df = combine_ohtani(batters_df, pitchers_df)
    all_players = pd.concat([batters_df, pitchers_df], ignore_index=True)
    all_players = all_players.sort_values(['dollars', 'rpts'], ascending=[False, False])
    all_players = all_players.reset_index(drop=True)
    all_players['rank'] = range(1, len(all_players) + 1)

    best_positions = []
    for _, row in all_players.iterrows():
        if row['type'] == 'pitcher':
            best_positions.append(row.get('pitcher_role', 'SP'))
        elif row['type'] == 'two-way':
            best_positions.append('DH')
        else:
            best_positions.append(pick_display_pos(row['positions']))
    all_players['best_pos'] = best_positions

    above_repl = sum(1 for _, r in all_players.iterrows() if r['dollars'] > 0)
    print(f"  Total: {len(all_players)}, Above replacement: {above_repl}")
    return all_players


# =============================================================================
# SNAPSHOT MANAGEMENT
# =============================================================================

def save_snapshot(players_list, date_str):
    if PREVIEW_LOCAL:
        print("  Local preview mode: skipping tracker snapshot write")
        return
    os.makedirs(TRACKER_DIR, exist_ok=True)
    filepath = os.path.join(TRACKER_DIR, f"{date_str}.json")
    snapshot = {
        'date': date_str,
        'timestamp': datetime.now().isoformat(),
        'players': players_list,
    }
    with open(filepath, 'w') as f:
        json.dump(snapshot, f, indent=2)
    print(f"  Snapshot saved: {filepath}")


def load_previous_snapshot(current_date_str):
    if not os.path.exists(TRACKER_DIR):
        return None
    files = sorted(f for f in os.listdir(TRACKER_DIR) if f.endswith('.json'))
    # Find most recent snapshot before current date
    prev_file = None
    for f in files:
        file_date = f.replace('.json', '')
        if file_date < current_date_str:
            prev_file = f
    if not prev_file:
        return None
    filepath = os.path.join(TRACKER_DIR, prev_file)
    with open(filepath, 'r') as f:
        return json.load(f)


def load_latest_snapshot():
    """Load the newest dated tracker snapshot for cache-only previews."""
    if not os.path.exists(TRACKER_DIR):
        return None
    files = sorted(
        f for f in os.listdir(TRACKER_DIR)
        if re.match(r'^\d{4}-\d{2}-\d{2}\.json$', f)
    )
    if not files:
        return None
    filepath = os.path.join(TRACKER_DIR, files[-1])
    with open(filepath, 'r') as f:
        return json.load(f)


def load_oldest_snapshot():
    """Load the earliest snapshot to compute cumulative changes over the full tracking period."""
    if not os.path.exists(TRACKER_DIR):
        return None
    files = sorted(f for f in os.listdir(TRACKER_DIR) if f.endswith('.json'))
    if not files:
        return None
    filepath = os.path.join(TRACKER_DIR, files[0])
    with open(filepath, 'r') as f:
        return json.load(f)


def compute_deltas(current_players, previous_snapshot):
    if not previous_snapshot:
        return {}, None

    prev_by_fg_id = {}
    prev_by_name = {}
    for p in previous_snapshot['players']:
        fg_id = p.get('fg_id', '')
        if fg_id:
            prev_by_fg_id[fg_id] = p
        prev_by_name[normalize_name(p['name'])] = p

    deltas = {}
    for p in current_players:
        fg_id = p.get('fg_id', '')
        name = p['name']

        prev = prev_by_fg_id.get(fg_id) or prev_by_name.get(normalize_name(name))
        if prev:
            deltas[fg_id or name] = {
                'dollar_change': round(p['dollars'] - prev['dollars'], 1),
                'rpts_change': round(p['rpts'] - prev['rpts'], 1),
                'rank_change': prev['rank'] - p['rank'],  # positive = improved
                'prev_dollars': prev['dollars'],
                'prev_rank': prev['rank'],
            }

    return deltas, previous_snapshot.get('date', '?')


def compute_cumulative_deltas(current_players, oldest_snapshot):
    """Compute cumulative changes from the oldest snapshot to now.

    This catches players who rise/fall steadily day-over-day but never
    make a big single-day move — e.g., +$0.3/day for 2 weeks = +$4.2 total.
    """
    if not oldest_snapshot:
        return {}, None

    old_by_fg_id = {}
    old_by_name = {}
    for p in oldest_snapshot['players']:
        fg_id = p.get('fg_id', '')
        if fg_id:
            old_by_fg_id[fg_id] = p
        old_by_name[normalize_name(p['name'])] = p

    cum_deltas = {}
    for p in current_players:
        fg_id = p.get('fg_id', '')
        name = p['name']

        old = old_by_fg_id.get(fg_id) or old_by_name.get(normalize_name(name))
        if old:
            cum_deltas[fg_id or name] = {
                'total_dollar_change': round(p['dollars'] - old['dollars'], 1),
                'total_rpts_change': round(p['rpts'] - old['rpts'], 1),
                'total_rank_change': old['rank'] - p['rank'],
                'first_dollars': old['dollars'],
                'first_rank': old['rank'],
            }

    return cum_deltas, oldest_snapshot.get('date', '?')


# =============================================================================
# STREAMING: PROCESSING
# =============================================================================

def get_streaming_window():
    """Get a rolling 5-day look-ahead window for streaming decisions."""
    today = date.today()
    end = today + timedelta(days=4)
    return today.isoformat(), end.isoformat()


def compute_pts_per_start(proj):
    """Calculate expected fantasy points per start from FG component projections."""
    gs = proj.get('GS', 1)
    if gs < 1:
        gs = 1
    ip = proj.get('IP', 0)
    # If IP/GS ratio is unrealistic (pitcher projected for relief + starts),
    # use IP/6.0 as a more realistic start count
    if ip / gs > 7.5:
        gs = max(gs, ip / 6.0)
    return (
        (proj['IP'] / gs) * PIT_SCORING['IP'] +
        (proj['H'] / gs) * PIT_SCORING['H'] +
        (proj['ER'] / gs) * PIT_SCORING['ER'] +
        (proj['BB'] / gs) * PIT_SCORING['BB'] +
        (proj['SO'] / gs) * PIT_SCORING['K'] +
        (proj['W'] / gs) * PIT_SCORING['W'] +
        (proj['L'] / gs) * PIT_SCORING['L']
    )


PROJECTION_MIN_GS = 5
PROJECTION_IP_PER_GS_SOFT_LIMIT = 7.5
PROJECTION_IP_PER_GS_HARD_LIMIT = 9.0


def _append_note(existing, note):
    if not note:
        return existing
    if not existing:
        return note
    if note in existing:
        return existing
    return f"{existing}; {note}"


def projection_sanity_status(proj, probable_source=None, roster_status=None):
    """Decide whether a probable starter's projection row is safe enough to score."""
    proj_gs = _safe_float((proj or {}).get('GS')) or 0.0
    proj_ip = _safe_float((proj or {}).get('IP')) or 0.0
    out = {
        'status': 'kept',
        'note': '',
        'original_ip_per_gs': None,
        'adjusted_ip_per_gs': None,
        'projected_gs': proj_gs,
        'projected_ip': proj_ip,
        'soft_limit': PROJECTION_IP_PER_GS_SOFT_LIMIT,
        'hard_limit': PROJECTION_IP_PER_GS_HARD_LIMIT,
    }
    if proj_gs < PROJECTION_MIN_GS:
        out.update({
            'status': 'dropped',
            'note': f"projected GS {proj_gs:g} is below starter threshold {PROJECTION_MIN_GS}",
        })
        return out
    if proj_ip <= 0:
        return out

    ip_per_gs = proj_ip / max(proj_gs, 1.0)
    out['original_ip_per_gs'] = round(ip_per_gs, 3)
    out['adjusted_ip_per_gs'] = round(ip_per_gs, 3)
    if ip_per_gs <= PROJECTION_IP_PER_GS_SOFT_LIMIT:
        return out
    if ip_per_gs > PROJECTION_IP_PER_GS_HARD_LIMIT:
        out.update({
            'status': 'dropped',
            'note': (
                f"projected IP/GS {ip_per_gs:.2f} exceeds hard sanity limit "
                f"{PROJECTION_IP_PER_GS_HARD_LIMIT:.1f}"
            ),
        })
        return out

    adjusted_gs = max(proj_gs, proj_ip / 6.0)
    adjusted_ip_per_gs = proj_ip / max(adjusted_gs, 1.0)
    out['status'] = 'clamped'
    out['adjusted_ip_per_gs'] = round(adjusted_ip_per_gs, 3)
    source_text = probable_source or 'unknown source'
    roster_text = roster_status or 'unknown status'
    out['note'] = (
        f"projection sanity clamp: IP/GS {ip_per_gs:.2f} exceeds "
        f"{PROJECTION_IP_PER_GS_SOFT_LIMIT:.1f}; kept because source={source_text}, "
        f"status={roster_text}; scoring uses adjusted IP/GS {adjusted_ip_per_gs:.2f}"
    )
    return out


def adjust_for_matchup(base_pts, proj, opp_factor):
    """Adjust per-start points based on opponent offense quality."""
    gs = max(proj.get('GS', 1), 1)
    ip = proj.get('IP', 0)
    if ip / gs > 7.5:
        gs = max(gs, ip / 6.0)
    # Negative components per start (hits + earned runs)
    h_per_gs = proj['H'] / gs
    er_per_gs = proj['ER'] / gs
    bb_per_gs = proj['BB'] / gs
    # Scale the damage components by opponent factor
    # opp_factor > 1 = tough lineup, < 1 = weak lineup
    damage_adj = (h_per_gs * -1 + er_per_gs * -2 + bb_per_gs * -1) * (opp_factor - 1)
    return round(base_pts + damage_adj, 1)


def classify_pitcher(proj):
    """Classify pitcher floor/ceiling from projection profile."""
    era = proj.get('ERA', 5.0)
    whip = proj.get('WHIP', 1.5)
    bb9 = proj.get('BB9', 4.0)
    k9 = proj.get('K9', 7.0)
    safe = era < 3.50 and whip < 1.15 and bb9 < 2.5
    upside = k9 > 9.5
    if safe and upside:
        return 'ACE'
    elif safe:
        return 'SAFE'
    elif upside:
        return 'UPSIDE'
    return ''


def assess_trend(proj, recent):
    """Assess recent form vs projection. Returns 'hot', 'cold', or ''.

    Bug fix: previously a high recent K/9 would trigger HOT even if ERA
    was much worse than projection (Senga had 8.83 L14D ERA but high K/9 ->
    incorrectly labeled HOT). Now HOT requires ERA isn't blowing up, and
    K/9 alone can only signal HOT when ERA is at least near projection.
    """
    if not recent:
        return ''
    try:
        recent_ip = float(recent.get('IP') or 0.0)
    except Exception:
        recent_ip = 0.0
    try:
        recent_starts = float(recent.get('GS')) if recent.get('GS') not in (None, '') else None
    except Exception:
        recent_starts = None
    if recent_starts is not None:
        if recent_starts < RECENT_TREND_MIN_STARTS:
            return ''
    elif recent_ip < RECENT_TREND_MIN_IP_FALLBACK:
        return ''
    proj_era = proj.get('ERA', 4.0)
    recent_era = recent.get('ERA', proj_era)
    proj_k9 = proj.get('K9', 8.0)
    recent_k9 = recent.get('K9', proj_k9)

    # COLD takes priority — if recent ERA is significantly worse, label cold
    # even if K/9 is up.
    if recent_era >= proj_era + 1.5:
        return 'cold'
    # HOT only when recent ERA is at or below projection (with small slack)
    if recent_era <= proj_era + 0.3 and (
        recent_era <= proj_era - 1.0 or recent_k9 >= proj_k9 + 2.0
    ):
        return 'hot'
    return ''


def assess_emerging(proj, recent, base_pts):
    """Detect pitchers outperforming their projection in a sustainable way.

    Flags FA streamers worth holding onto rather than cycling.
    The whole point is to catch guys whose projections haven't caught up to
    their actual performance — like a Taj Bradley who keeps putting up 10+ pt
    starts but ATC still projects him as mediocre. So we use lenient
    projection thresholds and focus on recent performance quality.

    Two paths to qualify:
    1. Standard: beating projection by 1+ ERA, decent K rate, not terrible proj
    2. Dominant: crushing projection by 2+ ERA with elite K rate (any proj)
    """
    if not recent:
        return False
    proj_era = proj.get('ERA', 4.5)
    recent_era = recent.get('ERA', proj_era)
    recent_k9 = recent.get('K9', 0)
    recent_ip = recent.get('IP', 0)

    # Need enough innings to matter (at least one full start in L14D)
    if recent_ip < 5:
        return False

    # Recent ERA must be substantially better than projection
    era_beat = proj_era - recent_era
    if era_beat < 1.0:
        return False

    # K rate must be legit (high K = real stuff, not just weak contact luck)
    if recent_k9 < 6.5:
        return False

    # Path 1 (standard): moderate outperformance + decent projection floor
    # base_pts >= 7.0 means "not a complete junk arm per projections"
    if era_beat >= 1.0 and recent_k9 >= 7.0 and base_pts >= 7.0:
        return True

    # Path 2 (dominant): crushing it so hard projections are irrelevant
    # 2+ ERA beat + 8+ K/9 = real breakout regardless of projection
    if era_beat >= 2.0 and recent_k9 >= 8.0:
        return True

    return False


def build_global_emerging_map(fg_proj, recent_form, roster_map, espn_matches, espn_id_to_roster):
    """Assess emerging/HOLD status for ALL relevant SPs, regardless of upcoming starts.

    This catches the Brandon Sproat case: a pitcher who just had a great start
    but doesn't have another scheduled start in the streaming window. He still
    qualifies as a HOLD based on recent performance, and we want to flag him so
    the user knows not to drop him.

    Only assesses pitchers who are MY ROSTER or FA — pitchers on other teams
    aren't actionable for the user.

    Returns: {normalized_pitcher_name: True}
    """
    # Build normalized lookup of espn matches for status checks
    espn_matches_norm = {}
    for fg_name, match_info in espn_matches.items():
        norm = normalize_name(fg_name)
        espn_matches_norm[norm] = (fg_name, match_info)

    emerging_set = set()
    for key, proj in fg_proj.items():
        fg_name = proj.get('name', '')
        fg_name_norm = normalize_name(fg_name)

        # Determine fantasy status
        match_entry = None
        if fg_name in espn_matches:
            match_entry = espn_matches[fg_name]
        elif fg_name_norm in espn_matches_norm:
            _, match_entry = espn_matches_norm[fg_name_norm]
        else:
            best = process.extractOne(
                fg_name_norm, list(espn_matches_norm.keys()),
                scorer=fuzz.token_sort_ratio, score_cutoff=80
            )
            if best:
                _, match_entry = espn_matches_norm[best[0]]

        status = 'OTHER'
        if match_entry:
            eid = match_entry['espn_id']
            if eid in espn_id_to_roster:
                if espn_id_to_roster[eid]['team_id'] == ESPN_TEAM_ID:
                    status = 'MY ROSTER'
                else:
                    status = 'OTHER'
            else:
                status = 'FA'
        else:
            status = 'FA'

        # Skip pitchers we can't act on
        if status not in ('FA', 'MY ROSTER'):
            continue

        # Skip openers/bulk relievers
        proj_gs = proj.get('GS', 0)
        proj_ip = proj.get('IP', 0)
        if proj_gs < 5 or (proj_ip > 0 and proj_ip / max(proj_gs, 1) > 7.5):
            continue

        recent = recent_form.get(key) or recent_form.get(fg_name_norm)
        base_pts = compute_pts_per_start(proj)

        if assess_emerging(proj, recent, base_pts):
            emerging_set.add(fg_name_norm)

    return emerging_set


def assess_platoon(pitcher_details, opp_handedness):
    """Assess platoon advantage/risk. Returns 'edge', 'risk', or ''."""
    if not pitcher_details or not opp_handedness:
        return ''
    vs_l = pitcher_details.get('career_vs_l', {})
    vs_r = pitcher_details.get('career_vs_r', {})
    if not vs_l or not vs_r:
        return ''

    try:
        ops_l = float(vs_l.get('ops', '.700'))
        ops_r = float(vs_r.get('ops', '.700'))
    except (ValueError, TypeError):
        return ''

    # Significant split = 100+ point OPS difference
    split_diff = ops_l - ops_r
    opp_left_pct = opp_handedness.get('left_pct', 30)

    if split_diff > 0.100 and opp_left_pct >= 40:
        return 'risk'  # Weak vs LHB and opponent is lefty-heavy
    if split_diff > 0.100 and opp_left_pct < 25:
        return 'edge'  # Weak vs LHB but opponent is righty-heavy
    if split_diff < -0.100 and opp_left_pct >= 40:
        return 'edge'  # Strong vs LHB and opponent is lefty-heavy
    if split_diff < -0.100 and opp_left_pct < 25:
        return 'risk'  # Strong vs LHB but opponent is righty-heavy (weak vs R)
    return ''


def analyze_pitch_matchup(mlb_id, opp_team, savant_data):
    """Analyze how a pitcher's arsenal matches up against an opponent.

    Returns dict with:
      - pitches: list of {code, name, usage, whiff, woba, grade, opp_woba, opp_whiff, matchup}
      - pitch_matchup_score: float (-1 to +1, positive = pitcher advantage)
      - summary: short string like "Arsenal Edge: elite slider vs SL-weak team"
    """
    if not savant_data:
        return None

    pitcher_arsenal = savant_data.get('pitcher', {}).get(str(mlb_id), {})
    if not pitcher_arsenal:
        return None

    team_bat = savant_data.get('team_batting', {}).get(opp_team, {})
    league_avgs = savant_data.get('league_avgs', {})

    PITCH_NAMES = {
        'FF': '4-Seam', 'SI': 'Sinker', 'SL': 'Slider', 'CU': 'Curve',
        'CH': 'Change', 'FC': 'Cutter', 'FS': 'Splitter', 'ST': 'Sweeper',
    }

    pitches = []
    matchup_components = []
    best_pitch = None
    best_matchup = None

    for code, stats in pitcher_arsenal.items():
        usage = stats.get('usage') or 0
        if usage < 5:
            continue  # Skip rare pitches

        whiff = stats.get('whiff')
        woba = stats.get('woba')
        rv100 = stats.get('rv100')

        # Grade the pitch quality vs league average
        lg = league_avgs.get(code, {})
        lg_whiff = lg.get('whiff', 25)
        lg_woba = lg.get('woba', 0.320)

        grade = ''
        if whiff is not None and woba is not None:
            whiff_diff = whiff - lg_whiff
            woba_diff = lg_woba - woba  # lower wOBA = better for pitcher
            if whiff_diff >= 8 and woba_diff >= 0.030:
                grade = 'elite'
            elif whiff_diff >= 4 or woba_diff >= 0.020:
                grade = 'plus'
            elif whiff_diff <= -6 or woba_diff <= -0.040:
                grade = 'weak'

        # Opponent batting vs this pitch type
        opp = team_bat.get(code, {})
        opp_woba = opp.get('woba')
        opp_whiff = opp.get('whiff')

        # Pitch matchup: pitcher quality + opponent vulnerability
        matchup = ''
        matchup_val = 0
        if woba is not None and opp_woba is not None and lg_woba > 0:
            # Pitcher's pitch quality (negative wOBA diff = better pitcher)
            pitch_quality = (lg_woba - woba) / lg_woba
            # Opponent vulnerability (negative = team struggles, positive = team mashes)
            opp_vuln = (lg_woba - opp_woba) / lg_woba if opp_woba else 0
            # Combined: positive = pitcher advantage
            matchup_val = (pitch_quality + opp_vuln) / 2
            if matchup_val >= 0.08:
                matchup = 'strong'
            elif matchup_val >= 0.03:
                matchup = 'favorable'
            elif matchup_val <= -0.08:
                matchup = 'poor'
            elif matchup_val <= -0.03:
                matchup = 'unfavorable'

        # Weight by usage for overall score
        weight = usage / 100.0
        matchup_components.append(matchup_val * weight)

        pitch_info = {
            'code': code, 'name': PITCH_NAMES.get(code, code),
            'usage': round(usage, 1),
            'whiff': round(whiff, 1) if whiff is not None else None,
            'woba': round(woba, 3) if woba is not None else None,
            'grade': grade,
            'opp_woba': round(opp_woba, 3) if opp_woba is not None else None,
            'opp_whiff': round(opp_whiff, 1) if opp_whiff is not None else None,
            'matchup': matchup,
        }
        pitches.append(pitch_info)

        # Track best pitch and best matchup for summary
        if grade in ('elite', 'plus') and (best_pitch is None or usage > best_pitch.get('usage', 0)):
            best_pitch = pitch_info
        if matchup in ('strong', 'favorable') and (best_matchup is None or matchup_val > best_matchup[1]):
            best_matchup = (pitch_info, matchup_val)

    if not pitches:
        return None

    # Sort by usage descending
    pitches.sort(key=lambda p: -(p.get('usage') or 0))

    # Overall pitch matchup score
    total_score = sum(matchup_components)

    # Build summary
    summary = ''
    poor_pitches = [p for p in pitches if p['matchup'] == 'poor']
    strong_pitches = [p for p in pitches if p['matchup'] in ('strong', 'favorable')]

    if best_matchup:
        matchup_pitch = best_matchup[0]
        grade = matchup_pitch.get('grade')
        grade_prefix = f"{grade} " if grade in ('elite', 'plus') else ""
        summary = f"Arsenal edge: {grade_prefix}{matchup_pitch['name'].lower()} fits well vs {opp_team}"
    elif best_pitch:
        summary = f"Has {best_pitch['grade']} {best_pitch['name'].lower()} ({best_pitch['whiff']}% whiff)"
    elif poor_pitches and len(poor_pitches) >= 2:
        summary = f"Arsenal concern: {opp_team} hits {poor_pitches[0]['name'].lower()}s and {poor_pitches[1]['name'].lower()}s well"
    elif poor_pitches:
        summary = f"Concern: {opp_team} mashes {poor_pitches[0]['name'].lower()}s ({poor_pitches[0].get('opp_woba', '?')} wOBA)"
    elif strong_pitches:
        summary = f"{strong_pitches[0]['name']} plays well vs {opp_team}"

    return {
        'pitches': pitches,
        'pitch_matchup_score': round(total_score, 3),
        'summary': summary,
    }


def classify_tier(pts, pitch_matchup_score=0):
    """Classify a start into a recommendation tier.

    Tiers based on matchup-adjusted pts/start plus pitch matchup bonus:
      - Must Start: 14+ pts (ace-level output expected)
      - Start: 10-14 pts (solid with favorable factors)
      - Borderline: 8-10 pts (risky but playable if desperate)
      - Sit: <8 pts (downside outweighs upside)
    """
    # Pitch matchup nudges the boundaries by up to 1.5 pts
    adj = pitch_matchup_score * 15  # scale ~0.1 score to ~1.5 pts
    effective = pts + adj

    if effective >= 14:
        return 'must_start'
    elif effective >= 10:
        return 'start'
    elif effective >= 8:
        return 'borderline'
    else:
        return 'avoid'


TIER_LABELS = {
    'must_start': 'Must Start',
    'start': 'Start',
    'borderline': 'Borderline',
    'avoid': 'Sit',
}

TIER_ORDER = {'must_start': 0, 'start': 1, 'borderline': 2, 'avoid': 3}
PROBABLE_SOURCE_RANK = {'mlb': 3, 'espn': 2, 'inferred_roster': 1, None: 0, '': 0}
MIN_STARTER_REST_DAYS = 4
HARD_START_EVIDENCE_SOURCES = {'completed_start', 'mlb_game_log', 'predictions_outcomes'}
SOFT_START_EVIDENCE_SOURCES = {'prediction_log_recent_start', 'predictions_outcomes_recent_log'}


def _probable_game_label(game):
    return (
        f"{game.get('date')} {game.get('pitcher_team') or '?'} "
        f"{'vs' if game.get('home_away') == 'H' else 'at'} {game.get('opponent') or '?'} "
        f"source={game.get('probable_source') or 'unknown'}"
    )


def _probable_assignment_id(game):
    return (
        game.get('date'),
        normalize_name(game.get('pitcher_name') or ''),
        game.get('pitcher_team'),
        game.get('opponent'),
        game.get('home_away'),
        game.get('game_pk'),
    )


def _recent_completed_starts_map(*dated_line_sets):
    """Combine completed-start dicts into {normalized pitcher: latest start info}."""
    out = {}
    for date_iso, lines in dated_line_sets:
        for norm, line in (lines or {}).items():
            if not norm:
                continue
            prior = out.get(norm)
            if prior is None or str(date_iso) > str(prior.get('date') or ''):
                out[norm] = {
                    'date': date_iso,
                    'name': line.get('name') or norm,
                    'team': line.get('team'),
                    'source': line.get('source') or 'completed_start',
                }
    return out


def _recent_actual_starts_from_workload(pitcher_workload, max_start_date=None):
    """Return latest actual starts from workload/game-log history by pitcher.

    Workload entries are already built from postgame outcomes and MLB game logs.
    This helper is read-only and is only used to sanity-check probable dates.
    """
    out = {}
    for norm, entry in (pitcher_workload or {}).items():
        if not norm:
            continue
        for start in (entry or {}).get('starts') or []:
            start_date = str(start.get('date') or '')[:10]
            if not start_date:
                continue
            if max_start_date and start_date > str(max_start_date)[:10]:
                continue
            prior = out.get(norm)
            if prior is None or start_date > str(prior.get('date') or ''):
                out[norm] = {
                    'date': start_date,
                    'name': start.get('name') or norm,
                    'team': start.get('team'),
                    'source': start.get('source') or 'workload_history',
                }
    return out


def _recent_actual_starts_from_outcomes(outcomes_log):
    """Read latest completed starts from predictions_outcomes.jsonl."""
    out = {}
    if not outcomes_log or not os.path.exists(outcomes_log):
        return out
    try:
        with open(outcomes_log) as f:
            for line in f:
                try:
                    row = json.loads(line)
                except Exception:
                    continue
                if row.get('no_start') or row.get('actual_pts') is None:
                    continue
                norm = normalize_name(row.get('name') or row.get('pitcher_name') or '')
                start_date = str(row.get('date') or row.get('game_date') or '')[:10]
                if not norm or not start_date:
                    continue
                prior = out.get(norm)
                if prior is None or start_date > str(prior.get('date') or ''):
                    out[norm] = {
                        'date': start_date,
                        'name': row.get('name') or row.get('pitcher_name') or norm,
                        'team': row.get('team'),
                        'source': 'predictions_outcomes',
                    }
    except Exception:
        return out
    return out


def _recent_logged_start_evidence_from_outcomes(outcomes_log, dates=None):
    """Read recent logged prediction/outcome rows as weak start-date evidence."""
    wanted_dates = {str(d)[:10] for d in (dates or []) if d}
    out = {}
    if not outcomes_log or not os.path.exists(outcomes_log):
        return out
    try:
        with open(outcomes_log) as f:
            for line in f:
                try:
                    row = json.loads(line)
                except Exception:
                    continue
                norm = normalize_name(row.get('name') or row.get('pitcher_name') or '')
                start_date = str(row.get('date') or row.get('game_date') or '')[:10]
                if not norm or not start_date:
                    continue
                if wanted_dates and start_date not in wanted_dates:
                    continue
                prior = out.get(norm)
                if prior is None or start_date > str(prior.get('date') or ''):
                    source = 'predictions_outcomes'
                    if row.get('no_start') or row.get('actual_pts') is None:
                        source = 'predictions_outcomes_recent_log'
                    out[norm] = {
                        'date': start_date,
                        'name': row.get('name') or row.get('pitcher_name') or norm,
                        'team': row.get('team'),
                        'source': source,
                    }
    except Exception:
        return out
    return out


def _merge_recent_start_maps(*maps):
    out = {}
    for mapping in maps:
        for norm, info in (mapping or {}).items():
            if not norm or not info or not info.get('date'):
                continue
            prior = out.get(norm)
            if prior is None or str(info.get('date')) > str(prior.get('date') or ''):
                out[norm] = dict(info)
    return out


def _recent_start_before_date(norm, target_date, *maps):
    if not target_date:
        return None
    latest = None
    target_iso = str(target_date)[:10]
    for mapping in maps:
        info = (mapping or {}).get(norm)
        if not info or not info.get('date'):
            continue
        start_iso = str(info.get('date'))[:10]
        if start_iso >= target_iso:
            continue
        if latest is None or start_iso > str(latest.get('date') or ''):
            latest = dict(info)
    return latest


def _recent_start_reason_label(source):
    if source in {'prediction_log_recent_start', 'predictions_outcomes_recent_log'}:
        return 'recent logged probable/start'
    return 'actual start'


def _start_evidence_reliability(source):
    parts = {p for p in str(source or '').split('+') if p}
    if parts & HARD_START_EVIDENCE_SOURCES:
        return 'hard'
    if parts & SOFT_START_EVIDENCE_SOURCES:
        return 'soft'
    return 'soft'


def _split_recent_start_evidence(mapping):
    hard = {}
    soft = {}
    for norm, info in (mapping or {}).items():
        if _start_evidence_reliability((info or {}).get('source')) == 'hard':
            hard[norm] = dict(info)
        else:
            soft[norm] = dict(info)
    return hard, soft


def _recent_prediction_start_evidence(dates):
    """Read-only fallback evidence for pitchers already projected today/yesterday."""
    out = {}
    for date_iso in dates or []:
        rows, _ = _latest_prediction_records_by_date(date_iso)
        for rec in rows:
            if rec.get('tbd'):
                continue
            norm = normalize_name(rec.get('name') or rec.get('pitcher_name') or '')
            if not norm:
                continue
            prior = out.get(norm)
            if prior is None or str(date_iso) > str(prior.get('date') or ''):
                out[norm] = {
                    'date': date_iso,
                    'name': rec.get('name') or rec.get('pitcher_name'),
                    'team': rec.get('team'),
                    'source': 'prediction_log_recent_start',
                }
    return out


def _suppress_probable_game(game, note, pitcher_name=None):
    out = dict(game)
    out['probable_conflict_pitcher'] = pitcher_name or out.get('pitcher_name')
    out['probable_note'] = note
    out['probable_conflict'] = True
    out['pitcher_name'] = None
    out['pitcher_mlb_id'] = None
    return out


def _validate_probable_schedule(schedule, recent_completed_starts=None,
                                pitcher_workload=None, verbose=True, example_limit=8):
    """Suppress clearly stale or conflicting probable assignments before scoring.

    This leaves projection math untouched; it only prevents low-confidence
    pitcher/date assignments from becoming normal actionable starts.
    """
    hard_recent_starts, soft_recent_starts = _split_recent_start_evidence(recent_completed_starts or {})
    workload_hard, workload_soft = _split_recent_start_evidence(_recent_actual_starts_from_workload(pitcher_workload))
    hard_recent_starts = _merge_recent_start_maps(hard_recent_starts, workload_hard)
    soft_recent_starts = _merge_recent_start_maps(soft_recent_starts, workload_soft)
    suppressed = {}
    warnings = {}
    examples = []
    warning_examples = []

    by_pitcher = defaultdict(list)
    for game in schedule or []:
        norm = normalize_name(game.get('pitcher_name') or '')
        if norm:
            by_pitcher[norm].append(game)

    def mark(game, reason):
        key = _probable_assignment_id(game)
        if key in suppressed:
            return
        suppressed[key] = reason
        if len(examples) < example_limit:
            examples.append({
                'pitcher': game.get('pitcher_name'),
                'reason': reason,
                'assignment': _probable_game_label(game),
            })

    def warn(game, reason):
        key = _probable_assignment_id(game)
        if key in warnings or key in suppressed:
            return
        warnings[key] = reason
        if len(warning_examples) < example_limit:
            warning_examples.append({
                'pitcher': game.get('pitcher_name'),
                'reason': reason,
                'assignment': _probable_game_label(game),
            })

    # Suppress projected starts 1-3 calendar days after a real completed start
    # from boxscore/outcome/workload history. Runtime probable sources can go
    # stale; source code must not trust them over completed-start evidence.
    for norm, games in by_pitcher.items():
        for game in games:
            try:
                game_date = date.fromisoformat(str(game.get('date'))[:10])
            except Exception:
                continue
            completed = _recent_start_before_date(
                norm,
                game_date.isoformat(),
                hard_recent_starts,
            )
            soft_completed = _recent_start_before_date(
                norm,
                game_date.isoformat(),
                soft_recent_starts,
            )

            def rest_conflict(info):
                if not info or not info.get('date'):
                    return None, None
                try:
                    prior_date = date.fromisoformat(str(info.get('date'))[:10])
                except Exception:
                    return None, None
                days = (game_date - prior_date).days
                if 1 <= days < MIN_STARTER_REST_DAYS:
                    return prior_date, days
                return None, None

            completed_date, days_since = rest_conflict(completed)
            if completed_date is not None:
                source = completed.get('source') or 'recent_start'
                evidence_label = _recent_start_reason_label(source)
                mark(
                    game,
                    (
                        f"recent-start conflict: {evidence_label} {completed_date.isoformat()} "
                        f"from {source}, projected again after {days_since} day(s) "
                        f"with source={game.get('probable_source') or 'unknown'}; "
                        "converted to TBD/problem"
                    ),
                )
                continue

            soft_date, soft_days = rest_conflict(soft_completed)
            if soft_date is not None:
                source = soft_completed.get('source') or 'recent_start'
                msg = (
                    f"prior prediction-log conflict: {soft_date.isoformat()} "
                    f"from {source}, projected again after {soft_days} day(s) "
                    f"with source={game.get('probable_source') or 'unknown'}; verify manually"
                )
                if game.get('probable_source') == 'mlb':
                    warn(game, msg)
                else:
                    mark(game, msg + "; converted to TBD/problem")

    # Suppress duplicate pitcher assignments too close together. MLB official
    # probable data wins over ESPN; otherwise keep the earlier assignment.
    duplicate_conflicts = 0
    for norm, games in by_pitcher.items():
        games = sorted(games, key=lambda g: (g.get('date') or '', -PROBABLE_SOURCE_RANK.get(g.get('probable_source'), 0)))
        for i, left in enumerate(games):
            if _probable_assignment_id(left) in suppressed:
                continue
            for right in games[i + 1:]:
                if _probable_assignment_id(right) in suppressed:
                    continue
                try:
                    left_date = date.fromisoformat(str(left.get('date'))[:10])
                    right_date = date.fromisoformat(str(right.get('date'))[:10])
                except Exception:
                    continue
                day_gap = abs((right_date - left_date).days)
                if day_gap > 3:
                    continue
                duplicate_conflicts += 1
                left_rank = PROBABLE_SOURCE_RANK.get(left.get('probable_source'), 0)
                right_rank = PROBABLE_SOURCE_RANK.get(right.get('probable_source'), 0)
                if left_rank > right_rank:
                    drop, keep = right, left
                elif right_rank > left_rank:
                    drop, keep = left, right
                else:
                    drop, keep = (right, left) if str(left.get('date')) <= str(right.get('date')) else (left, right)
                mark(
                    drop,
                    (
                        "probable-date conflict: "
                        f"kept {_probable_game_label(keep)} over {_probable_game_label(drop)}"
                    ),
                )

    validated = []
    for game in schedule or []:
        key = _probable_assignment_id(game)
        reason = suppressed.get(key)
        if reason:
            validated.append(_suppress_probable_game(game, reason))
        else:
            warning = warnings.get(key)
            if warning:
                game = dict(game)
                game['probable_warning'] = warning
            validated.append(game)

    stale_count = sum(
        1 for reason in suppressed.values()
        if str(reason).startswith(('stale probable', 'recent-start conflict', 'prior prediction-log conflict'))
    )
    report = {
        'duplicate_conflicts': duplicate_conflicts,
        'recent_rest_conflicts': stale_count,
        'stale_suppressed': stale_count,
        'soft_warnings': len(warnings),
        'suppressed_total': len(suppressed),
        'examples': examples,
        'warning_examples': warning_examples,
        'suppressed': suppressed,
        'warnings': warnings,
    }
    if verbose:
        print(
            "  Probable date sanity: "
            f"{duplicate_conflicts} duplicate pitcher-date conflict(s), "
            f"{len(suppressed)} total start(s) suppressed, "
            f"{stale_count} stale/recent-rest probable start(s), "
            f"{len(warnings)} soft warning(s)"
        )
        for ex in examples:
            print(f"    - {ex['pitcher']}: {ex['reason']} ({ex['assignment']})")
        for ex in warning_examples:
            print(f"    - warning {ex['pitcher']}: {ex['reason']} ({ex['assignment']})")
    return validated, report


def _resolve_probable_schedule(schedule, espn_probables=None, my_sps_by_team=None):
    """Fill MLB TBD slots from current ESPN probables or conservative roster inference."""
    resolved = []
    pitcher_start_dates = {
        game.get('pitcher_name'): game.get('date')
        for game in schedule or []
        if game.get('pitcher_name') and game.get('date')
    }
    my_sps_by_team = my_sps_by_team or {}
    for game in schedule or []:
        game = dict(game)
        if game.get('pitcher_name'):
            resolved.append(game)
            continue
        team = game.get('pitcher_team')
        pitcher_name = None
        if espn_probables:
            esp_name = espn_probables.get((game.get('date'), team))
            if esp_name:
                pitcher_name = esp_name
                game['pitcher_name'] = esp_name
                game['probable_source'] = 'espn'
                pitcher_start_dates[esp_name] = game.get('date')
        if not pitcher_name and team in my_sps_by_team:
            candidates = my_sps_by_team[team]
            try:
                game_date = date.fromisoformat(game.get('date'))
            except Exception:
                game_date = None
            available = []
            for n, p, m in candidates:
                prev_date_str = pitcher_start_dates.get(n)
                if game_date and prev_date_str:
                    prev_date = date.fromisoformat(prev_date_str)
                    if abs((game_date - prev_date).days) < 5:
                        continue
                available.append((n, p, m))
            if len(available) == 1:
                fg_name, proj, match_entry = available[0]
                game['pitcher_name'] = fg_name
                game['probable_source'] = 'inferred_roster'
                pitcher_start_dates[fg_name] = game.get('date')
        resolved.append(game)
    return resolved


def _my_starting_pitchers_by_team(fg_proj, roster_map, espn_matches):
    my_sps_by_team = {}
    if not roster_map:
        return my_sps_by_team
    espn_matches_norm = {}
    for fg_name, match_info in (espn_matches or {}).items():
        espn_matches_norm[normalize_name(fg_name)] = (fg_name, match_info)
    for key, proj in (fg_proj or {}).items():
        fg_name = proj.get('name', '')
        fg_name_norm = normalize_name(fg_name)
        match_entry = None
        if fg_name in (espn_matches or {}):
            match_entry = espn_matches[fg_name]
        elif fg_name_norm in espn_matches_norm:
            _, match_entry = espn_matches_norm[fg_name_norm]
        if match_entry:
            eid = match_entry['espn_id']
            if eid in roster_map and roster_map[eid]['team_id'] == ESPN_TEAM_ID:
                p_team = proj.get('team', '') or (key.split('|')[-1] if '|' in key else '')
                if proj.get('GS', 0) >= 5 and p_team:
                    my_sps_by_team.setdefault(p_team, []).append((fg_name, proj, match_entry))
    return my_sps_by_team


def build_streaming_data(schedule, fg_proj, recent_form, team_offense,
                         league_avg_ops, team_handedness, pitcher_details,
                         roster_map, espn_matches, savant_data=None,
                         team_il_hitters=None, team_il_returns=None,
                         global_emerging=None, espn_probables=None,
                         learned_biases=None, savant_advanced=None,
                         fg_pitching_plus=None, team_bullpens=None,
                         pitcher_workload=None, recent_completed_starts=None):
    """Build the full streaming dataset for the week."""
    _runtime_prediction_records.clear()
    # Build lookup from FG name to ESPN match data
    espn_id_to_roster = roster_map or {}

    # Build normalized lookup for espn_matches (handles accent/nickname differences)
    espn_matches_norm = {}
    for fg_name, match_info in espn_matches.items():
        norm = normalize_name(fg_name)
        espn_matches_norm[norm] = (fg_name, match_info)

    # Build a reverse lookup: normalized name+team -> FG projection key
    fg_by_name = {}
    for key, proj in fg_proj.items():
        fg_by_name[key] = proj
        # Also index by just name for fallback
        name_only = key.split('|')[0]
        if name_only not in fg_by_name:
            fg_by_name[name_only] = proj

    # Build lookup of MY ROSTER SPs by team for TBD resolution
    # When MLB hasn't announced a probable pitcher but the user knows their guy is starting,
    # we can infer it by matching the TBD team to the user's rostered SP on that team.
    my_sps_by_team = _my_starting_pitchers_by_team(fg_proj, roster_map, espn_matches)

    schedule = _resolve_probable_schedule(schedule, espn_probables, my_sps_by_team)
    schedule, probable_sanity = _validate_probable_schedule(
        schedule,
        recent_completed_starts=recent_completed_starts,
        pitcher_workload=pitcher_workload,
    )

    streaming = []
    for game in schedule:
        pitcher_name = game.get('pitcher_name')
        if not pitcher_name:
            team = game['pitcher_team']
            streaming.append({
                'date': game['date'], 'day': game['day'],
                'name': 'TBD', 'team': team,
                'opponent': game['opponent'], 'home_away': game['home_away'],
                'tbd': True,
                'probable_note': game.get('probable_note'),
                'probable_conflict_pitcher': game.get('probable_conflict_pitcher'),
                'probable_source': game.get('probable_source'),
                'probable_warning': game.get('probable_warning'),
            })
            continue

        pitcher_team = game['pitcher_team']
        norm_key = f"{normalize_name(pitcher_name)}|{pitcher_team}"
        proj = fg_by_name.get(norm_key) or fg_by_name.get(normalize_name(pitcher_name))
        if not proj:
            continue  # Can't score without projections

        # Determine fantasy status using normalized name matching
        fg_name = proj['name']
        fg_name_norm = normalize_name(fg_name)
        status = 'OTHER'
        match_entry = None
        if fg_name in espn_matches:
            match_entry = espn_matches[fg_name]
        elif fg_name_norm in espn_matches_norm:
            _, match_entry = espn_matches_norm[fg_name_norm]
        else:
            # Fuzzy fallback for nickname mismatches (Cam vs Cameron)
            best = process.extractOne(
                fg_name_norm, list(espn_matches_norm.keys()),
                scorer=fuzz.token_sort_ratio, score_cutoff=80
            )
            if best:
                _, match_entry = espn_matches_norm[best[0]]

        if match_entry:
            eid = match_entry['espn_id']
            if eid in espn_id_to_roster:
                info = espn_id_to_roster[eid]
                if info['team_id'] == ESPN_TEAM_ID:
                    status = 'MY ROSTER'
                else:
                    status = info.get('team_name', 'Rostered')
            else:
                status = 'FA'
        else:
            status = 'FA'

        # Skip only truly bad/opening projection rows. Small IP/GS violations
        # on real probable starters are kept with the same per-start adjustment
        # compute_pts_per_start() has always used, so official/rostered starts
        # do not silently disappear from the report.
        projection_sanity = projection_sanity_status(
            proj,
            probable_source=game.get('probable_source'),
            roster_status=status,
        )
        if projection_sanity.get('status') == 'dropped':
            continue
        probable_warning = _append_note(game.get('probable_warning'), projection_sanity.get('note'))

        # NOTE: We compute features + prediction for EVERY scheduled SP (not
        # just FA/MY ROSTER) so the learning engine has ~30 starts/day of
        # ground truth to calibrate against. The streaming display still
        # filters down at the end.

        # Compute scores
        base_pts = compute_pts_per_start(proj)
        opp = game['opponent']
        opp_stats = team_offense.get(opp, {})
        # Use regressed OPS (blends actual with league avg based on sample size)
        opp_ops = opp_stats.get('ops_regressed', opp_stats.get('ops', league_avg_ops))
        opp_factor = opp_ops / league_avg_ops if league_avg_ops > 0 else 1.0

        # Park factor: game is at the home team's ballpark
        home_team = game['pitcher_team'] if game['home_away'] == 'H' else opp
        park_factor = PARK_FACTORS.get(home_team, 1.0)

        # Combined adjustment: opponent quality * park factor
        combined_factor = opp_factor * park_factor
        adj_pts = adjust_for_matchup(base_pts, proj, combined_factor)

        # Tags and context
        tag = classify_pitcher(proj)
        recent = recent_form.get(norm_key) or recent_form.get(normalize_name(pitcher_name))
        trend = assess_trend(proj, recent)
        # Use global emerging map if available (covers all FA + roster SPs)
        # so per-game streaming display matches the global HOLD assessment.
        if global_emerging is not None:
            emerging = fg_name_norm in global_emerging
        else:
            emerging = assess_emerging(proj, recent, base_pts) if status in ('FA', 'MY ROSTER') else False

        # Pitcher details (splits + arsenal)
        mlb_id = game.get('pitcher_mlb_id') or proj.get('mlb_id')
        details = pitcher_details.get(str(mlb_id), {}) if mlb_id else {}
        opp_hand = team_handedness.get(opp, {})
        platoon = assess_platoon(details, opp_hand)

        # Career split OPS
        vs_l_ops = details.get('career_vs_l', {}).get('ops', '')
        vs_r_ops = details.get('career_vs_r', {}).get('ops', '')

        # Pitch matchup analysis
        pitch_analysis = analyze_pitch_matchup(mlb_id, opp, savant_data) if mlb_id else None
        pitch_matchup_score = pitch_analysis['pitch_matchup_score'] if pitch_analysis else 0
        pitch_adj = pitch_matchup_score * 15
        effective_pts = adj_pts + pitch_adj
        tier = classify_tier(adj_pts, pitch_matchup_score)

        # Notable IL hitters on the opponent
        opp_il = []
        if team_il_hitters and opp in team_il_hitters:
            opp_il = team_il_hitters[opp]

        # Recently activated stars on the opponent — recent team OPS won't reflect them yet
        opp_il_returns = []
        if team_il_returns and opp in team_il_returns:
            opp_il_returns = team_il_returns[opp]

        # Pre-adjustment ("rule-based") prediction. This is what the learning
        # engine uses for residual computation; never gets fed back on itself.
        pts_pre_adj = effective_pts

        # Apply learned biases (from accumulated outcomes) — auto-correct for
        # any feature buckets where the model has been systematically off.
        learned_adj_total = 0.0
        adjustments_applied = []
        if learned_biases:
            preview_entry = {
                'name': fg_name, 'tier': tier, 'opp_rank': opp_stats.get('ops_rank', 15),
                'park_factor': park_factor, 'platoon': platoon, 'tag': tag,
                'trend': trend, 'home_away': game['home_away'],
            }
            learned_adj_total, adjustments_applied = apply_learned_biases(
                preview_entry, learned_biases
            )

        # Final pts = effective + learned correction
        final_pts = pts_pre_adj + learned_adj_total
        # Re-classify tier with the corrected pts so the recommendation reflects
        # what we actually expect to happen.
        if learned_adj_total != 0:
            tier = classify_tier(final_pts - pitch_adj, pitch_matchup_score)

        weather_venue = _logged_weather_venue_context(game)

        entry = {
            'date': game['date'], 'day': game['day'],
            'name': fg_name, 'team': pitcher_team,
            'opponent': opp, 'home_away': game['home_away'],
            'game_pk': game.get('game_pk'),
            'pitcher_id': mlb_id,
            'pitcher_hand': game.get('pitcher_hand') or details.get('pitcher_hand'),
            'pts': round(final_pts, 1),
            'pts_pre_adj': round(pts_pre_adj, 1),
            'adj_total': round(learned_adj_total, 2),
            'adjustments': [
                {'label': a.get('label', ''), 'delta': a.get('delta_applied', a.get('mean', 0)),
                 'n': a.get('n'), 'basis': a.get('basis')}
                for a in adjustments_applied
            ],
            'base_pts': round(adj_pts, 1),
            'era': round(proj['ERA'], 2), 'whip': round(proj['WHIP'], 3),
            'k9': round(proj['K9'], 1),
            'opp_ops': f"{opp_ops:.3f}",
            'opp_ops_raw': f"{opp_stats.get('ops', league_avg_ops):.3f}",
            'opp_rank': opp_stats.get('ops_rank', 15),
            'opp_k_pct': f"{opp_stats.get('k_pct', 0.20):.1%}",
            'park': home_team,
            'park_factor': park_factor,
            'platoon': platoon,
            'opp_hand': f"{opp_hand.get('left_pct', '?')}% L" if opp_hand else '',
            'vs_l_ops': vs_l_ops, 'vs_r_ops': vs_r_ops,
            'splits_window_years': details.get('splits_window_years'),
            'tag': tag,
            'trend': trend,
            'recent_era': round(recent['ERA'], 2) if recent else None,
            'recent_ip': round(recent.get('IP'), 1) if recent and recent.get('IP') is not None else None,
            'recent_k9': round(recent.get('K9'), 1) if recent and recent.get('K9') is not None else None,
            'fb_velo': details.get('fb_velo'),
            'pitch_count': details.get('pitch_count', 0),
            'status': status,
            'tbd': False,
            'tier': tier,
            'tier_label': TIER_LABELS.get(tier, ''),
            'probable_source': game.get('probable_source'),
            'probable_warning': probable_warning,
            'projection_sanity_status': projection_sanity.get('status'),
            'projection_ip_per_gs': projection_sanity.get('original_ip_per_gs'),
            'projection_adjusted_ip_per_gs': projection_sanity.get('adjusted_ip_per_gs'),
            'projection_sanity_note': projection_sanity.get('note'),
            'pitch_analysis': pitch_analysis,
            'emerging': emerging,
            'opp_il': opp_il,
            'opp_il_returns': opp_il_returns,
            **weather_venue,
        }

        # Phase 2 enrichment: attach advanced features for auto-correlation
        # discovery. Each one becomes a candidate feature the bias engine
        # quartile-buckets and tests for residual signal.
        try:
            mlb_id_str = str(mlb_id) if mlb_id else None
            sa = (savant_advanced or {}).get(mlb_id_str, {}) if mlb_id_str else {}
            fg_pp_key = f"{normalize_name(fg_name)}|{pitcher_team}"
            fpp = (fg_pitching_plus or {}).get(fg_pp_key, {})
            opp_bp = (team_bullpens or {}).get(opp, {})
            wl = (pitcher_workload or {}).get(normalize_name(fg_name), {})

            entry.update({
                # Statcast advanced
                'xera': sa.get('xera'),
                'xwoba': sa.get('xwoba'),
                'xba': sa.get('xba'),
                'xslg': sa.get('xslg'),
                'barrel_pct': sa.get('barrel_pct'),
                'hard_hit_pct': sa.get('hard_hit_pct'),
                'whiff_pct': sa.get('whiff_pct'),
                'k_pct_savant': sa.get('k_pct'),
                'bb_pct_savant': sa.get('bb_pct'),
                'chase_pct': sa.get('chase_pct'),
                'gb_pct': sa.get('gb_pct'),
                'fb_pct': sa.get('fb_pct'),
                'ld_pct': sa.get('ld_pct'),
                # FG advanced
                'stuff_plus': fpp.get('stuff_plus'),
                'location_plus': fpp.get('location_plus'),
                'pitching_plus': fpp.get('pitching_plus'),
                'fip': fpp.get('fip'),
                'xfip': fpp.get('xfip'),
                'siera': fpp.get('siera'),
                # Opponent bullpen (affects W/L probability)
                'opp_bullpen_era': opp_bp.get('era'),
                'opp_bullpen_whip': opp_bp.get('whip'),
                # Workload
                'last_pitch_count': wl.get('last_pitch_count'),
                **_workload_features_for_game(wl, game['date']),
            })
        except Exception:
            pass

        # Log prediction for EVERY scheduled SP (not just FA/MY ROSTER) so the
        # learning engine has full league-wide ground truth to calibrate against.
        log_prediction(entry)

        # Recommendation layer: make the visible start/sit tier more
        # conservative when the backtested risk guard fires. This does not
        # alter points, learned corrections, or stored prediction logs.
        entry = apply_visible_risk_guard_overlay(entry)

        # Streaming UI only shows FA + MY ROSTER (the only ones you'd act on)
        if status in ('FA', 'MY ROSTER'):
            streaming.append(entry)

    # Sort by date, then by tier, then by pts descending within each tier
    streaming.sort(key=lambda s: (s['date'], TIER_ORDER.get(s.get('tier', 'avoid'), 3), -(s.get('pts') or -999)))
    # Flush all buffered predictions to disk as one JSONL per game date
    flush_predictions()
    return streaming


def _logged_weather_venue_context(game):
    """Return logged-only weather/venue fields from already-fetched schedule data."""
    game = dict(game or {})
    game_features = _features_with_venue_metadata(game, game)
    roof_type = game_features.get('roof_type')
    is_dome = game_features.get('is_indoor_or_dome')
    if isinstance(roof_type, str) and roof_type.strip():
        is_dome = roof_type.strip().lower() in {'dome', 'fixed roof', 'indoor', 'retractable'}
    context = {
        'game_datetime': game_features.get('game_datetime') or game.get('game_time'),
        'venue_name': game_features.get('venue_name'),
        'venue_lat': _safe_float(game_features.get('venue_lat')),
        'venue_lon': _safe_float(game_features.get('venue_lon')),
        'roof_type': roof_type,
        'roof_status': game.get('roof_status'),
        'is_indoor_or_dome': is_dome,
    }
    context.update(_logged_outdoor_weather_snapshot(context))
    return context


# =============================================================================
# HTML REPORT GENERATION
# =============================================================================

def prediction_feature_log_status():
    """Summarize whether the newest prediction log contains future-learning fields."""
    workload_fields = {
        'days_rest', 'last_start_ip', 'last_start_pitch_count',
        'avg_ip_last_3_starts', 'avg_pitch_count_last_3_starts',
        'workload_risk_score', 'workload_note',
    }
    weather_fields = {
        'game_datetime', 'venue_name', 'roof_type', 'roof_status',
        'is_indoor_or_dome', 'weather_source', 'weather_snapshot_time',
        'weather_temp_f', 'weather_wind_speed_mph', 'weather_wind_direction',
        'weather_run_boost', 'weather_hr_boost', 'weather_note',
    }
    try:
        files = _recent_prediction_files(limit=1)
        if not files:
            return "Newest prediction log: not found."
        seen = set()
        with open(files[0]) as f:
            for line in f:
                if not line.strip():
                    continue
                try:
                    seen.update((json.loads(line).get('features') or {}).keys())
                except Exception:
                    continue
        workload = 'yes' if seen & workload_fields else 'no'
        weather = 'yes' if seen & weather_fields else 'no'
        return f"Newest prediction log includes workload fields: {workload}; weather/roof fields: {weather}."
    except Exception:
        return "Newest prediction log field status unavailable."


def _fast_preview_float(value, default=0.0):
    if value in (None, ''):
        return default
    try:
        return float(value)
    except (TypeError, ValueError):
        return default


def _fast_preview_streaming_entry(record):
    features = record.get('features') or {}
    game_date = record.get('date') or record.get('game_date') or ''
    try:
        day_label = datetime.strptime(game_date, '%Y-%m-%d').strftime('%a')
    except Exception:
        day_label = ''
    pts = _fast_preview_float(record.get('predicted_pts') or record.get('final_pts'), 0.0)
    recent_era = features.get('recent_era')
    entry = {
        'date': game_date,
        'day': day_label,
        'name': record.get('name') or record.get('pitcher_name') or '',
        'team': record.get('team') or '',
        'opponent': record.get('opponent') or '',
        'home_away': record.get('home_away') or '',
        'pts': pts,
        'pts_pre_adj': _fast_preview_float(record.get('predicted_pts_raw') or record.get('base_pts'), pts),
        'adj_total': _fast_preview_float(record.get('adj_total'), 0.0),
        'adjustments': record.get('adjustments') or [],
        'tier': record.get('tier') or 'borderline',
        'status': record.get('status') or '',
        'features': features,
        'tbd': False,
        'era': _fast_preview_float(features.get('proj_era') or recent_era, 0.0),
        'k9': _fast_preview_float(features.get('proj_k9') or features.get('recent_k9'), 0.0),
        'opp_ops': str(features.get('opp_ops') or features.get('opp_ops_raw') or '--'),
        'opp_rank': int(_fast_preview_float(features.get('opp_rank'), 15)),
        'park_factor': _fast_preview_float(features.get('park_factor'), 1.0),
        'park': features.get('park') or '',
        'platoon': features.get('platoon') or '',
        'opp_hand': features.get('opp_hand') or '',
        'vs_l_ops': features.get('vs_l_ops'),
        'vs_r_ops': features.get('vs_r_ops'),
        'splits_window_years': features.get('splits_window_years'),
        'tag': features.get('tag') or '',
        'trend': features.get('trend') or '',
        'recent_era': _fast_preview_float(recent_era, None) if recent_era is not None else None,
        'emerging': bool(features.get('emerging')),
        'fb_velo': _fast_preview_float(features.get('fb_velo'), None) if features.get('fb_velo') is not None else None,
        'pitch_count': features.get('pitch_count'),
        'opp_il': [],
        'opp_il_returns': [],
        'pitch_analysis': None,
    }
    return apply_visible_risk_guard_overlay(entry)


def load_prediction_logs_for_fast_preview():
    """Build usable streaming rows from existing prediction logs without fetching."""
    if not os.path.isdir(PREDICTIONS_DIR):
        return [], None
    latest = {}
    date_values = set()
    for fn in sorted(os.listdir(PREDICTIONS_DIR)):
        if not fn.endswith('.jsonl'):
            continue
        path = os.path.join(PREDICTIONS_DIR, fn)
        try:
            with open(path) as f:
                for line in f:
                    if not line.strip():
                        continue
                    try:
                        rec = json.loads(line)
                    except Exception:
                        continue
                    if rec.get('date'):
                        date_values.add(rec.get('date'))
                    key = (
                        rec.get('date'),
                        normalize_name(rec.get('name') or rec.get('pitcher_name') or ''),
                        rec.get('team'),
                        rec.get('opponent'),
                        rec.get('home_away'),
                    )
                    latest[key] = rec
        except Exception:
            continue
    rows = [_fast_preview_streaming_entry(rec) for rec in latest.values()]
    rows.sort(key=lambda s: (s.get('date') or '', TIER_ORDER.get(s.get('tier', 'avoid'), 3), -(s.get('pts') or 0)))
    if date_values:
        dates = sorted(date_values)
        date_range = dates[0] if dates[0] == dates[-1] else f"{dates[0]} through {dates[-1]}"
    else:
        date_range = None
    return rows, date_range


def _latest_prediction_records_by_date(target_date=None):
    """Read prediction JSONL rows for one date and keep the latest per start."""
    target_date = target_date or date.today().isoformat()
    path = os.path.join(PREDICTIONS_DIR, f'{target_date}.jsonl')
    if not os.path.exists(path):
        return [], path
    latest = {}
    try:
        with open(path) as f:
            for line in f:
                if not line.strip():
                    continue
                try:
                    rec = json.loads(line)
                except Exception:
                    continue
                key = (
                    rec.get('date') or rec.get('game_date') or target_date,
                    normalize_name(rec.get('name') or rec.get('pitcher_name') or ''),
                    rec.get('team'),
                    rec.get('opponent'),
                    rec.get('home_away'),
                )
                prior = latest.get(key)
                if prior is None or str(rec.get('logged_at') or '') >= str(prior.get('logged_at') or ''):
                    latest[key] = rec
    except Exception:
        return [], path
    return list(latest.values()), path


def _feature_float(features, key, default=None):
    value = (features or {}).get(key)
    if value in (None, ''):
        return default
    try:
        return float(value)
    except (TypeError, ValueError):
        return default


def _compact_decision_text(value, limit=72):
    text = re.sub(r'\s+', ' ', str(value or '')).strip()
    if len(text) <= limit:
        return text
    clipped = text[:limit].rsplit(' ', 1)[0].rstrip(' ,;:-')
    return (clipped or text[:limit].rstrip()) + '...'


def _decision_risk_boost_flags(record):
    features = record.get('features') or {}
    risks = []
    boosts = []
    tier = record.get('tier') or ''
    opp_rank = _feature_float(features, 'opp_rank')
    park_factor = _feature_float(features, 'park_factor')
    recent_era = _feature_float(features, 'recent_era')
    workload_risk = _feature_float(features, 'workload_risk_score')
    pitch_matchup = _feature_float(features, 'pitch_matchup_score')
    opp_il_count = _feature_float(features, 'opp_il_count', 0) or 0
    opp_il_returns = _feature_float(features, 'opp_il_returns_count', 0) or 0

    if tier == 'avoid':
        risks.append('avoid tier')
    elif tier == 'borderline':
        risks.append('borderline tier')
    if opp_rank is not None:
        if opp_rank <= 10:
            risks.append(f'tough offense rank {int(opp_rank)}')
        elif opp_rank >= 21:
            boosts.append(f'soft offense rank {int(opp_rank)}')
    if park_factor is not None:
        if park_factor >= 1.05:
            risks.append(f'hitter park {park_factor:.2f}')
        elif park_factor <= 0.96:
            boosts.append(f'pitcher park {park_factor:.2f}')
    if features.get('platoon') == 'risk':
        risks.append('platoon risk')
    elif features.get('platoon') == 'edge':
        boosts.append('platoon edge')
    if features.get('trend') == 'cold':
        risks.append('cold recent trend')
    elif features.get('trend') == 'hot':
        boosts.append('hot recent trend')
    if recent_era is not None:
        if recent_era >= 5.0:
            risks.append(f'recent ERA {recent_era:.2f}')
        elif recent_era <= 3.5:
            boosts.append(f'recent ERA {recent_era:.2f}')
    if workload_risk is not None and workload_risk >= 0.6:
        risks.append(f'workload risk {workload_risk:.2f}')
    if features.get('workload_note') and workload_risk is not None and workload_risk >= 0.4:
        risks.append(_compact_decision_text(features.get('workload_note'), 64))
    if pitch_matchup is not None:
        if pitch_matchup <= -0.05:
            risks.append(f'poor pitch matchup {pitch_matchup:+.2f}')
        elif pitch_matchup >= 0.05:
            boosts.append(f'good pitch matchup {pitch_matchup:+.2f}')
    if opp_il_count:
        boosts.append(f'opponent IL bats {int(opp_il_count)}')
    if opp_il_returns:
        risks.append(f'opponent bats returning {int(opp_il_returns)}')
    if features.get('tag'):
        boosts.append(str(features.get('tag')))
    return risks, boosts


def _risky_borderline_streamer_reasons(record, risks=None):
    """Display-only tag for Borderline FA/WAIVER streamers with backtested bust signals."""
    if (record.get('tier') or '') != 'borderline':
        return []
    if (record.get('status') or '') not in ('FA', 'WAIVER'):
        return []
    features = record.get('features') or {}
    reasons = []
    recent_era = _feature_float(features, 'recent_era')
    if features.get('trend') == 'cold':
        reasons.append('cold recent form')
    if recent_era is not None and recent_era >= 5.14:
        reasons.append(f'recent ERA {recent_era:.2f}')
    counted_risks = [
        r for r in (risks if risks is not None else _decision_risk_boost_flags(record)[0])
        if r not in ('borderline tier', 'borderline projection')
    ]
    if len(counted_risks) >= 2:
        reasons.append('multiple risk flags')
    return reasons[:3]


def _decision_points(record):
    return _fast_preview_float(record.get('predicted_pts') or record.get('final_pts') or record.get('pts'), 0.0)


RISK_GUARD_ADVICE_TO_TIER = {
    'START': 'start',
    'BORDERLINE': 'borderline',
    'SIT': 'avoid',
}


def _risk_guard_policy_features(record):
    """Feature subset used by the visible recommendation risk guard."""
    features = dict((record or {}).get('features') or {})
    defaults = {
        'opp_rank': record.get('opp_rank'),
        'park_factor': record.get('park_factor'),
        'recent_era': record.get('recent_era'),
        'proj_k9': record.get('proj_k9') or record.get('k9'),
        'k9': record.get('k9'),
        'workload_risk_score': record.get('workload_risk_score'),
        'platoon': record.get('platoon'),
        'trend': record.get('trend'),
    }
    pitch_analysis = record.get('pitch_analysis') or {}
    if isinstance(pitch_analysis, dict):
        defaults['pitch_matchup_score'] = pitch_analysis.get('pitch_matchup_score')
    for key, value in defaults.items():
        if features.get(key) in (None, '') and value not in (None, ''):
            features[key] = value
    return features


def apply_visible_risk_guard_overlay(record):
    """Apply the backtested risk guard to display recommendations only.

    The model's original tier remains available as model_tier; points and
    learned corrections are untouched.
    """
    if not isinstance(record, dict) or record.get('tbd'):
        return record
    out = dict(record)
    original_tier = out.get('model_tier') or out.get('tier') or 'borderline'
    points = _decision_points(out)
    features = _risk_guard_policy_features(out)
    decision_entry = {
        'pts': points,
        'tier': original_tier,
        'status': out.get('status'),
    }
    shadow = _shadow_risk_guard_decision(decision_entry, features)
    shadow_advice = shadow.get('shadow_risk_guard_advice')
    display_tier = RISK_GUARD_ADVICE_TO_TIER.get(shadow_advice, original_tier)
    changed = bool(shadow.get('shadow_risk_guard_changed') and display_tier != original_tier)

    out.setdefault('model_tier', original_tier)
    out.setdefault('model_tier_label', TIER_LABELS.get(original_tier, original_tier))
    out['shadow_risk_guard_advice'] = shadow_advice
    out['shadow_risk_guard_score'] = shadow.get('shadow_risk_guard_score')
    out['shadow_risk_guard_reasons'] = shadow.get('shadow_risk_guard_reasons') or []
    out['shadow_risk_guard_policy'] = shadow.get('shadow_risk_guard_policy')
    out['risk_guard_applied'] = changed
    out['risk_guard_original_tier'] = original_tier
    out['risk_guard_display_tier'] = display_tier
    out['risk_guard_reasons'] = shadow.get('shadow_risk_guard_reasons') or []
    out['risk_guard_policy'] = shadow.get('shadow_risk_guard_policy')
    if changed:
        out['tier'] = display_tier
        out['tier_label'] = TIER_LABELS.get(display_tier, display_tier)
        reason_text = ', '.join(out['risk_guard_reasons'][:3]) or 'multiple risk flags'
        policy_label = RISK_GUARD_WEIGHT_PRESETS_BY_KEY.get(
            out.get('risk_guard_policy') or '', {}
        ).get('label', 'Risk guard')
        out['risk_guard_note'] = (
            f"{policy_label} downgraded {TIER_LABELS.get(original_tier, original_tier)} "
            f"to {TIER_LABELS.get(display_tier, display_tier)}: {reason_text}"
        )
    return out


def _decision_status_key(record):
    return (
        normalize_name(record.get('name') or record.get('pitcher_name') or ''),
        record.get('team') or '',
    )


def _local_prediction_status_cache():
    """Build a read-only status cache from existing prediction logs."""
    cache = {}
    if not os.path.isdir(PREDICTIONS_DIR):
        return cache
    for fn in sorted(os.listdir(PREDICTIONS_DIR)):
        if not fn.endswith('.jsonl'):
            continue
        path = os.path.join(PREDICTIONS_DIR, fn)
        try:
            with open(path) as f:
                for line in f:
                    if not line.strip():
                        continue
                    try:
                        rec = json.loads(line)
                    except Exception:
                        continue
                    status = rec.get('status')
                    key = _decision_status_key(rec)
                    if status and key[0]:
                        cache[key] = status
        except Exception:
            continue
    return cache


def _load_local_roster_status_cache():
    """Read optional local roster/status cache files if a future workflow adds one."""
    candidates = [
        ROSTER_STATUS_CACHE_FILE,
        os.path.join(SCRIPT_DIR, 'espn_rosters.json'),
        os.path.join(SCRIPT_DIR, 'roster_map.json'),
        os.path.join(STREAMING_CACHE_DIR, 'espn_rosters.json'),
        os.path.join(STREAMING_CACHE_DIR, 'roster_map.json'),
    ]
    cache = {}
    sources = []
    for path in candidates:
        if not os.path.exists(path):
            continue
        sources.append(path)
        try:
            with open(path) as f:
                data = json.load(f)
        except Exception:
            continue
        if isinstance(data, dict) and isinstance(data.get('players'), list):
            rows = data.get('players') or []
        else:
            rows = data.values() if isinstance(data, dict) else data
        if not isinstance(rows, list) and not hasattr(rows, '__iter__'):
            continue
        for item in rows:
            if not isinstance(item, dict):
                continue
            name = item.get('name') or item.get('fullName') or item.get('player_name')
            team = item.get('team') or item.get('proTeam') or item.get('mlb_team') or ''
            status = item.get('status') or item.get('fantasy_status')
            team_id = item.get('team_id')
            if not status and team_id is not None:
                status = 'MY ROSTER' if team_id == ESPN_TEAM_ID else 'OTHER'
            if name and status:
                cache[(normalize_name(name), team)] = status
    return cache, sources


def _enrich_decision_statuses(records):
    """Fill blank statuses in memory only from local read-only status sources."""
    enriched = [dict(rec) for rec in records]
    prediction_cache = _local_prediction_status_cache()
    roster_cache, roster_sources = _load_local_roster_status_cache()
    prediction_enriched_count = 0
    roster_enriched_count = 0
    for rec in enriched:
        if rec.get('status'):
            continue
        status = roster_cache.get(_decision_status_key(rec))
        if status:
            rec['status'] = status
            rec['_status_enriched'] = True
            rec['_status_source'] = 'roster_status_cache'
            roster_enriched_count += 1
            continue
        status = prediction_cache.get(_decision_status_key(rec))
        if status:
            rec['status'] = status
            rec['_status_enriched'] = True
            rec['_status_source'] = 'prediction_log_history'
            prediction_enriched_count += 1

    return enriched, {
        'prediction_status_cache_rows': len(prediction_cache),
        'roster_status_cache_rows': len(roster_cache),
        'roster_status_cache_sources': roster_sources,
        'enriched_count': roster_enriched_count + prediction_enriched_count,
        'roster_enriched_count': roster_enriched_count,
        'prediction_enriched_count': prediction_enriched_count,
    }


def _format_decision_row(record):
    risks, boosts = _decision_risk_boost_flags(record)
    matchup = f"{record.get('home_away') or '?'} vs {record.get('opponent') or '?'}"
    if record.get('home_away') == 'A':
        matchup = f"A @ {record.get('opponent') or '?'}"
    elif record.get('home_away') == 'H':
        matchup = f"H vs {record.get('opponent') or '?'}"
    risk_text = '; '.join(risks[:4]) if risks else 'none'
    boost_text = '; '.join(boosts[:4]) if boosts else 'none'
    return (
        f"  - {record.get('name') or record.get('pitcher_name') or 'Unknown'} "
        f"({record.get('team') or '?'}, {record.get('status') or 'UNKNOWN'}) "
        f"{_decision_points(record):.1f} pts | {record.get('tier') or 'unknown'} | "
        f"{matchup} | risks: {risk_text} | boosts: {boost_text}"
    )


def _print_decision_section(title, rows, limit=None):
    print(f"\n{title}")
    if not rows:
        print("  None")
        return
    for rec in rows[:limit] if limit else rows:
        print(_format_decision_row(rec))


def _decision_record_from_streaming_entry(entry):
    """Make a report streaming row look like a prediction-log decision record."""
    if not isinstance(entry, dict):
        return {}
    features = dict(entry.get('features') or {})
    feature_defaults = {
        'proj_era': entry.get('era'),
        'proj_k9': entry.get('k9'),
        'opp_ops': entry.get('opp_ops'),
        'opp_rank': entry.get('opp_rank'),
        'park_factor': entry.get('park_factor'),
        'park': entry.get('park'),
        'platoon': entry.get('platoon'),
        'opp_hand': entry.get('opp_hand'),
        'vs_l_ops': entry.get('vs_l_ops'),
        'vs_r_ops': entry.get('vs_r_ops'),
        'splits_window_years': entry.get('splits_window_years'),
        'tag': entry.get('tag'),
        'trend': entry.get('trend'),
        'recent_era': entry.get('recent_era'),
        'fb_velo': entry.get('fb_velo'),
        'pitch_count': entry.get('pitch_count'),
        'emerging': entry.get('emerging'),
        'pitcher_hand': entry.get('pitcher_hand'),
        'opp_il_count': len(entry.get('opp_il', []) or []),
        'opp_il_returns_count': len(entry.get('opp_il_returns', []) or []),
    }
    for key, value in feature_defaults.items():
        if features.get(key) in (None, '') and value not in (None, ''):
            features[key] = value
    pitch_analysis = entry.get('pitch_analysis') or {}
    if isinstance(pitch_analysis, dict):
        features['pitch_matchup_score'] = pitch_analysis.get('pitch_matchup_score')
    for key in (
        'workload_risk_score', 'workload_note', 'days_rest',
        'last_start_ip', 'last_start_pitch_count',
        'avg_ip_last_3_starts', 'avg_pitch_count_last_3_starts',
        'max_pitch_count_last_5_starts', 'season_avg_ip_per_start',
        'season_avg_pitches_per_start', 'short_rest_flag',
        'extra_rest_flag', 'last_pitch_count',
    ):
        if key in entry:
            features[key] = entry.get(key)
    return {
        'logged_at': entry.get('logged_at'),
        'date': entry.get('date') or entry.get('game_date'),
        'name': entry.get('name') or entry.get('pitcher_name'),
        'team': entry.get('team'),
        'opponent': entry.get('opponent'),
        'home_away': entry.get('home_away'),
        'game_pk': entry.get('game_pk'),
        'pitcher_id': entry.get('pitcher_id'),
        'pitcher_hand': entry.get('pitcher_hand'),
        'predicted_pts': entry.get('predicted_pts', entry.get('pts')),
        'final_pts': entry.get('final_pts', entry.get('pts')),
        'predicted_pts_raw': entry.get('predicted_pts_raw', entry.get('pts_pre_adj')),
        'adj_total': entry.get('adj_total'),
        'adjustments': entry.get('adjustments') or [],
        'tier': entry.get('tier'),
        'model_tier': entry.get('model_tier'),
        'model_tier_label': entry.get('model_tier_label'),
        'risk_guard_applied': entry.get('risk_guard_applied'),
        'risk_guard_original_tier': entry.get('risk_guard_original_tier'),
        'risk_guard_display_tier': entry.get('risk_guard_display_tier'),
        'risk_guard_reasons': entry.get('risk_guard_reasons') or [],
        'risk_guard_note': entry.get('risk_guard_note'),
        'shadow_risk_guard_advice': entry.get('shadow_risk_guard_advice'),
        'shadow_risk_guard_score': entry.get('shadow_risk_guard_score'),
        'shadow_risk_guard_policy': entry.get('shadow_risk_guard_policy'),
        'status': entry.get('status'),
        'tbd': entry.get('tbd'),
        'probable_note': entry.get('probable_note'),
        'probable_conflict_pitcher': entry.get('probable_conflict_pitcher'),
        'probable_source': entry.get('probable_source'),
        'probable_warning': entry.get('probable_warning'),
        'features': features,
    }


def build_daily_decision_summary(target_date=None, records=None, source=None):
    """Build the read-only daily decision audit data shared by CLI and report."""
    target_date = target_date or date.today().isoformat()
    if records is None:
        records, path = _latest_prediction_records_by_date(target_date)
        source = source or path
    else:
        path = source or 'current report prediction records'
        records = [
            dict(r) for r in records
            if (r.get('date') or r.get('game_date') or target_date) == target_date
        ]
    records, probable_report = validate_probable_prediction_records(records, source=source or path)
    records = [apply_visible_risk_guard_overlay(dict(r)) for r in records]
    summary = {
        'date': target_date,
        'source': path,
        'records': records,
        'rows_scanned': len(records),
        'actionable': [],
        'fa_ranked': [],
        'roster_ranked': [],
        'risky_roster': [],
        'avoid_traps': [],
        'problems': [],
        'warning': None,
        'enrichment': {
            'prediction_status_cache_rows': 0,
            'roster_status_cache_rows': 0,
            'roster_status_cache_sources': [],
            'enriched_count': 0,
            'roster_enriched_count': 0,
            'prediction_enriched_count': 0,
        },
        'original_actionable': 0,
        'hidden_other_count': 0,
        'hidden_unknown_count': 0,
        'roster_count': 0,
        'fa_count': 0,
        'waiver_count': 0,
        'actionable_count': 0,
        'status_unreliable': False,
        'probable_sanity': probable_report,
    }
    if not records:
        summary['problems'].append('No prediction log found for today. Run a preview or normal tracker first to create current predictions.')
        summary['warning'] = summary['problems'][0]
        summary['status_unreliable'] = True
        return summary

    actionable_statuses = {'FA', 'MY ROSTER', 'WAIVER'}
    summary['original_actionable'] = sum(1 for r in records if r.get('status') in actionable_statuses)
    records, enrichment = _enrich_decision_statuses(records)
    summary['records'] = records
    summary['enrichment'] = enrichment
    actionable = [r for r in records if r.get('status') in actionable_statuses]
    unknown_status = [r for r in records if not r.get('status')]
    hidden_other = [r for r in records if r.get('status') and r.get('status') not in actionable_statuses]

    if not actionable or len(unknown_status) > len(records) * 0.25:
        summary['status_unreliable'] = True
        summary['warning'] = (
            'Some roster/FA statuses are unavailable; roster and waiver filtering may be unreliable. '
            'Run python3.11 -B engine/fantasy_tracker.py --preview-local or a normal tracker run to refresh statuses.'
        )

    fa_rows = [r for r in actionable if r.get('status') == 'FA']
    waiver_rows = [r for r in actionable if r.get('status') == 'WAIVER']
    roster_rows = [r for r in actionable if r.get('status') == 'MY ROSTER']
    available_rows = fa_rows + waiver_rows
    fa_ranked = sorted(available_rows, key=lambda r: (TIER_ORDER.get(r.get('tier', 'avoid'), 3), -_decision_points(r)))
    roster_ranked = sorted(roster_rows, key=lambda r: (TIER_ORDER.get(r.get('tier', 'avoid'), 3), -_decision_points(r)))
    risky_roster = sorted(
        [r for r in roster_rows if r.get('tier') in ('borderline', 'avoid') or _decision_risk_boost_flags(r)[0]],
        key=lambda r: (TIER_ORDER.get(r.get('tier', 'avoid'), 3), _decision_points(r))
    )
    avoid_traps = sorted(
        [r for r in available_rows if r.get('tier') == 'avoid' or len(_decision_risk_boost_flags(r)[0]) >= 2],
        key=lambda r: (_decision_points(r), -len(_decision_risk_boost_flags(r)[0]))
    )

    problems = []
    if unknown_status:
        problems.append(f"{len(unknown_status)} prediction rows have blank roster/FA status and were hidden from decisions.")
    if hidden_other:
        problems.append(f"{len(hidden_other)} rows appear rostered by other teams/OTHER and were hidden from actionable recommendations.")
    tbd_rows = [r for r in records if r.get('tbd') or (r.get('name') or r.get('pitcher_name') or '').upper() == 'TBD']
    if tbd_rows:
        for rec in tbd_rows:
            note = rec.get('probable_note')
            pitcher = rec.get('probable_conflict_pitcher')
            if note:
                detail = f" ({pitcher})" if pitcher else ""
                problems.append(f"{rec.get('team') or '?'} vs {rec.get('opponent') or '?'} has probable-date conflict{detail}: {note}.")
            else:
                problems.append(f"{rec.get('team') or '?'} vs {rec.get('opponent') or '?'} has TBD pitcher status.")
    else:
        problems.append("Existing prediction data does not include unresolved TBD slots; fresh tracker data is needed for live TBD discovery.")

    summary.update({
        'actionable': actionable,
        'fa_ranked': fa_ranked,
        'roster_ranked': roster_ranked,
        'risky_roster': risky_roster,
        'avoid_traps': avoid_traps,
        'problems': problems,
        'hidden_other_count': len(hidden_other),
        'hidden_unknown_count': len(unknown_status),
        'roster_count': len(roster_rows),
        'fa_count': len(fa_rows),
        'waiver_count': len(waiver_rows),
        'actionable_count': len(actionable),
    })
    return summary


def _decision_plain_reasons(record, risks=None, boosts=None, confidence=None):
    """Summarize logged decision signals in plain English for the report UI."""
    features = record.get('features') or {}
    pts = _decision_points(record)
    tier = record.get('tier') or 'borderline'
    confidence = confidence or {
        'must_start': 'Strong Start',
        'start': 'Start',
        'borderline': 'Borderline',
        'avoid': 'Avoid',
    }.get(tier, 'Borderline')
    risks = risks if risks is not None else _decision_risk_boost_flags(record)[0]
    boosts = boosts if boosts is not None else _decision_risk_boost_flags(record)[1]
    if record.get('risk_guard_applied'):
        reasons = record.get('risk_guard_reasons') or []
        from_label = TIER_LABELS.get(record.get('risk_guard_original_tier'), record.get('risk_guard_original_tier') or 'Start')
        to_label = TIER_LABELS.get(record.get('risk_guard_display_tier'), record.get('risk_guard_display_tier') or tier)
        main = f"Risk guard downgraded {from_label} to {to_label}"
        risk = f"Multiple bust flags: {', '.join(reasons[:3])}" if reasons else "Multiple logged bust-risk flags"
        return _compact_decision_text(main), _compact_decision_text(risk)

    opp_rank = _feature_float(features, 'opp_rank')
    opp_ops = features.get('opp_ops') or features.get('opp_ops_raw')
    park_factor = _feature_float(features, 'park_factor')
    pitch_matchup = _feature_float(features, 'pitch_matchup_score')
    workload_risk = _feature_float(features, 'workload_risk_score')
    adj_total = _safe_float(record.get('adj_total'))
    if adj_total is None:
        adjustments = record.get('adjustments') or []
        try:
            adj_total = sum(_safe_float(a.get('delta')) or 0 for a in adjustments if isinstance(a, dict))
        except Exception:
            adj_total = None

    boost_reasons = []
    if adj_total is not None and adj_total >= 0.3:
        boost_reasons.append(f"learned correction adds {adj_total:+.1f} pts")
    if pts >= 12:
        boost_reasons.append(f"projects for {pts:.1f} points")
    elif confidence in ('Strong Start', 'Start'):
        boost_reasons.append(f"{confidence.lower()} profile at {pts:.1f} projected points")
    if opp_rank is not None and opp_rank >= 21:
        detail = f"rank {int(opp_rank)}"
        if opp_ops:
            detail += f", {opp_ops} OPS"
        boost_reasons.append(f"soft opponent offense ({detail})")
    if park_factor is not None and park_factor <= 0.96:
        boost_reasons.append(f"pitcher-friendly park ({park_factor:.2f})")
    if features.get('platoon') == 'edge':
        boost_reasons.append("platoon edge")
    if features.get('trend') == 'hot':
        boost_reasons.append("hot recent form")
    if pitch_matchup is not None and pitch_matchup >= 0.05:
        boost_reasons.append("arsenal matches this opponent well")
    if _feature_float(features, 'opp_il_count', 0):
        boost_reasons.append("opponent is missing notable bats")
    if features.get('tag') in ('ACE', 'SAFE', 'UPSIDE'):
        boost_reasons.append(f"{features.get('tag').lower()} tag")

    risk_reasons = []
    if adj_total is not None and adj_total <= -0.3:
        risk_reasons.append(f"learned correction trims {adj_total:.1f} pts")
    if tier == 'avoid':
        risk_reasons.append("avoid-tier projection")
    elif tier == 'borderline':
        risk_reasons.append("borderline projection")
    if opp_rank is not None and opp_rank <= 10:
        detail = f"rank {int(opp_rank)}"
        if opp_ops:
            detail += f", {opp_ops} OPS"
        risk_reasons.append(f"tough opponent offense ({detail})")
    if park_factor is not None and park_factor >= 1.05:
        risk_reasons.append(f"hitter-friendly park ({park_factor:.2f})")
    if features.get('platoon') == 'risk':
        risk_reasons.append("platoon risk")
    if features.get('trend') == 'cold':
        risk_reasons.append("cold recent form")
    if pitch_matchup is not None and pitch_matchup <= -0.05:
        risk_reasons.append("arsenal matchup concern")
    if _feature_float(features, 'opp_il_returns_count', 0):
        risk_reasons.append("opponent has hitters returning")
    if workload_risk is not None and workload_risk >= 0.6:
        risk_reasons.append("elevated workload/leash risk")

    if not boost_reasons and boosts:
        boost_reasons.append(str(boosts[0]))
    if not risk_reasons and risks:
        risk_reasons.append(str(risks[0]))
    main_reason = boost_reasons[0] if boost_reasons else f"{confidence} based on {pts:.1f} projected points"
    risk_reason = risk_reasons[0] if risk_reasons else "No major red flag in logged signals"
    if tier == 'borderline':
        main_reason = f"Playable for volume, not a safe start at {pts:.1f} projected points"
        if not risk_reasons:
            risk_reason = "Borderline stream, not a priority add"
        risky_reasons = _risky_borderline_streamer_reasons(record, risks)
        if risky_reasons:
            main_reason = f"Avoid unless chasing volume at {pts:.1f} projected points"
            risk_reason = f"Backtest caution: {', '.join(risky_reasons)}"
    return _compact_decision_text(main_reason), _compact_decision_text(risk_reason)


def _decision_report_item(record):
    risks, boosts = _decision_risk_boost_flags(record)
    risky_borderline = _risky_borderline_streamer_reasons(record, risks)
    confidence = {
        'must_start': 'Strong Start',
        'start': 'Start',
        'borderline': 'Volume Only' if risky_borderline else 'Playable, Not Safe',
        'avoid': 'Avoid',
    }.get(record.get('tier'), 'Borderline')
    main_reason, risk_reason = _decision_plain_reasons(record, risks, boosts, confidence)
    return {
        'name': record.get('name') or record.get('pitcher_name') or 'Unknown',
        'team': record.get('team') or '',
        'opponent': record.get('opponent') or '',
        'home_away': record.get('home_away') or '',
        'status': record.get('status') or 'UNKNOWN',
        'tier': record.get('tier') or 'unknown',
        'confidence': confidence,
        'points': round(_decision_points(record), 1),
        'main_reason': main_reason,
        'risk_reason': risk_reason,
        'risks': risks[:3],
        'boosts': boosts[:3],
        'risk_guard_candidate': bool(risky_borderline),
        'risk_guard_reasons': (record.get('risk_guard_reasons') or risky_borderline),
        'risk_guard_applied': bool(record.get('risk_guard_applied')),
        'risk_guard_note': record.get('risk_guard_note'),
        'model_tier': record.get('model_tier'),
        '_matchup_source': record.get('_matchup_source'),
        '_matchup_snapshot_date': record.get('_matchup_snapshot_date') or _matchup_record_snapshot_date(record),
    }


def _mark_desperation_items(items):
    marked = []
    for item in items:
        if item.get('tier') == 'avoid':
            item = dict(item)
            item['watch_label'] = 'DESPERATION ONLY'
        marked.append(item)
    return marked


def _best_available_for_report(rows, limit=6):
    usable = [r for r in rows if r.get('tier') != 'avoid']
    selected = usable[:limit] if usable else rows[:limit]
    return _mark_desperation_items([_decision_report_item(r) for r in selected])


def _risky_roster_for_report(rows, limit=6):
    items = []
    for rec in rows[:limit]:
        item = _decision_report_item(rec)
        item['also_listed'] = True
        items.append(item)
    return items


def _decision_records_for_report(snapshot_date, streaming_data):
    """Return current report prediction-shaped records without changing storage."""
    if _runtime_prediction_records:
        records = [dict(rec) for rec in _runtime_prediction_records]
        records.extend(
            _decision_record_from_streaming_entry(s)
            for s in (streaming_data or [])
            if s.get('tbd') or s.get('probable_note')
        )
        return records, 'current run prediction records'
    if streaming_data:
        return [_decision_record_from_streaming_entry(s) for s in streaming_data], 'current report streaming rows'
    return [], 'prediction logs'


def _mark_probable_record_problem(record, reason):
    out = dict(record)
    out['probable_conflict_pitcher'] = out.get('name') or out.get('pitcher_name')
    out['probable_note'] = reason
    out['probable_conflict'] = True
    out['tbd'] = True
    out['name'] = 'TBD'
    out['pitcher_name'] = 'TBD'
    out['status'] = ''
    return out


def validate_probable_prediction_records(records, source='prediction records',
                                         recent_actual_starts=None,
                                         verbose=False, example_limit=8):
    """Read-time sanity filter for cached/current prediction-shaped records."""
    records = [dict(r) for r in records or []]
    hard_recent_starts, soft_recent_starts = _split_recent_start_evidence(recent_actual_starts or {})
    suppressed = {}
    warnings = {}
    examples = []
    warning_examples = []
    by_pitcher = defaultdict(list)
    for idx, rec in enumerate(records):
        if rec.get('tbd'):
            continue
        norm = normalize_name(rec.get('name') or rec.get('pitcher_name') or '')
        if norm:
            by_pitcher[norm].append((idx, rec))

    def mark(idx, rec, reason):
        if idx in suppressed:
            return
        suppressed[idx] = reason
        if len(examples) < example_limit:
            examples.append({
                'pitcher': rec.get('name') or rec.get('pitcher_name'),
                'date': rec.get('date') or rec.get('game_date'),
                'team': rec.get('team'),
                'opponent': rec.get('opponent'),
                'reason': reason,
                'source': source,
            })

    def warn(idx, rec, reason):
        if idx in suppressed or idx in warnings:
            return
        warnings[idx] = reason
        if len(warning_examples) < example_limit:
            warning_examples.append({
                'pitcher': rec.get('name') or rec.get('pitcher_name'),
                'date': rec.get('date') or rec.get('game_date'),
                'team': rec.get('team'),
                'opponent': rec.get('opponent'),
                'reason': reason,
                'source': source,
            })

    for norm, items in by_pitcher.items():
        for idx, rec in items:
            features = rec.get('features') or {}
            game_date_raw = rec.get('date') or rec.get('game_date')
            actual = _recent_start_before_date(norm, game_date_raw, hard_recent_starts)
            if actual and actual.get('date'):
                try:
                    game_date = date.fromisoformat(str(game_date_raw)[:10])
                    actual_date = date.fromisoformat(str(actual.get('date'))[:10])
                    days_since = (game_date - actual_date).days
                except Exception:
                    days_since = None
                if days_since is not None and 1 <= days_since < MIN_STARTER_REST_DAYS:
                    source_name = actual.get('source') or 'recent_start'
                    evidence_label = _recent_start_reason_label(source_name)
                    mark(
                        idx,
                        rec,
                        (
                            f"recent-start conflict: {evidence_label} {actual_date.isoformat()} "
                            f"from {source_name}, "
                            f"projected again after {days_since} day(s)"
                        ),
                    )
                    continue
            soft = _recent_start_before_date(norm, game_date_raw, soft_recent_starts)
            if soft and soft.get('date'):
                try:
                    game_date = date.fromisoformat(str(game_date_raw)[:10])
                    soft_date = date.fromisoformat(str(soft.get('date'))[:10])
                    days_since = (game_date - soft_date).days
                except Exception:
                    days_since = None
                if days_since is not None and 1 <= days_since < MIN_STARTER_REST_DAYS:
                    warn(
                        idx,
                        rec,
                        (
                            f"prior prediction-log conflict: {soft_date.isoformat()} "
                            f"from {soft.get('source') or 'recent_start'}, "
                            f"projected again after {days_since} day(s); verify manually"
                        ),
                    )
            days_rest = _feature_float(features, 'days_rest')
            if days_rest is not None and days_rest <= 3:
                mark(idx, rec, f"low-confidence probable date: only {days_rest:g} day(s) since last start")
        sorted_items = sorted(items, key=lambda item: (item[1].get('date') or item[1].get('game_date') or '', -_decision_points(item[1])))
        for i, (left_idx, left) in enumerate(sorted_items):
            if left_idx in suppressed:
                continue
            left_date_raw = left.get('date') or left.get('game_date')
            try:
                left_date = date.fromisoformat(str(left_date_raw)[:10])
            except Exception:
                continue
            for right_idx, right in sorted_items[i + 1:]:
                if right_idx in suppressed or right_idx in warnings:
                    continue
                right_date_raw = right.get('date') or right.get('game_date')
                try:
                    right_date = date.fromisoformat(str(right_date_raw)[:10])
                except Exception:
                    continue
                if abs((right_date - left_date).days) <= 3:
                    mark(
                        right_idx,
                        right,
                        f"probable-date conflict: also appears on {left_date.isoformat()}",
                    )

    out = [
        _mark_probable_record_problem(rec, suppressed[idx]) if idx in suppressed
        else {**rec, 'probable_warning': warnings[idx]} if idx in warnings
        else rec
        for idx, rec in enumerate(records)
    ]
    report = {
        'records_scanned': len(records),
        'suppressed_total': len(suppressed),
        'soft_warnings': len(warnings),
        'examples': examples,
        'warning_examples': warning_examples,
        'source': source,
    }
    if verbose:
        print(
            f"Probable date record sanity ({source}): "
            f"{len(suppressed)} low-confidence record(s) flagged, {len(warnings)} soft warning(s)"
        )
        for ex in examples:
            print(f"  - {ex['pitcher']} {ex['date']} {ex['team']} vs {ex['opponent']}: {ex['reason']}")
        for ex in warning_examples:
            print(f"  - warning {ex['pitcher']} {ex['date']} {ex['team']} vs {ex['opponent']}: {ex['reason']}")
    return out, report


def audit_probable_dates():
    """Read-only audit for impossible or stale probable pitcher dates in logs."""
    records = []
    files = _recent_prediction_files(limit=10)
    for path in files:
        target_date = os.path.basename(path).replace('.jsonl', '')
        rows, _ = _latest_prediction_records_by_date(target_date)
        records.extend(rows)
    recent_completed = []
    for offset in range(0, 4):
        d = (date.today() - timedelta(days=offset)).isoformat()
        recent_completed.append((d, fetch_completed_starts_for_date(d, verbose=False)))
    recent_dates = [
        (date.today() - timedelta(days=offset)).isoformat()
        for offset in range(0, 4)
    ]
    recent_actual_starts = _merge_recent_start_maps(
        _recent_actual_starts_from_outcomes(OUTCOMES_LOG),
        _recent_logged_start_evidence_from_outcomes(OUTCOMES_LOG, recent_dates),
        _recent_completed_starts_map(*recent_completed),
        _recent_prediction_start_evidence(recent_dates),
    )
    validated, report = validate_probable_prediction_records(
        records,
        source='recent prediction logs',
        recent_actual_starts=recent_actual_starts,
        verbose=False,
        example_limit=20,
    )
    print("PROBABLE DATE AUDIT")
    print("=" * 60)
    print("Read-only: inspects recent prediction logs for low-confidence pitcher/date assignments.")
    print(f"Prediction files scanned: {len(files)}")
    print(f"Prediction records scanned: {report['records_scanned']}")
    print(f"Recent actual/completed/logged starts checked: {len(recent_actual_starts)}")
    print(f"Low-confidence probable records flagged: {report['suppressed_total']}")
    print(f"Soft prediction-log warnings: {report.get('soft_warnings', 0)}")
    examples = report.get('examples') or []
    if examples:
        print("\nExamples")
        for ex in examples:
            print(
                f"  - {ex['pitcher']} on {ex['date']} "
                f"({ex['team']} vs {ex['opponent']}): {ex['reason']}"
            )
    else:
        print("\nNo impossible short-rest or duplicate-date patterns found in recent prediction logs.")
    warning_examples = report.get('warning_examples') or []
    if warning_examples:
        print("\nSoft warnings")
        for ex in warning_examples:
            print(
                f"  - {ex['pitcher']} on {ex['date']} "
                f"({ex['team']} vs {ex['opponent']}): {ex['reason']}"
            )
    names = {normalize_name(ex.get('pitcher') or ''): ex for ex in examples}
    for wanted in ('Chris Bassitt', 'Walbert Urena'):
        key = normalize_name(wanted)
        warning_names = {normalize_name(ex.get('pitcher') or ''): ex for ex in warning_examples}
        if key not in names and key not in warning_names:
            print(f"  - {wanted}: no recent conflict found in scanned logs.")
    return {'records': len(records), 'flagged': report['suppressed_total']}


def _status_for_probable_pitcher(name, team, fg_proj=None, espn_matches=None, roster_map=None):
    roster_cache, _ = _load_local_roster_status_cache()
    cached = roster_cache.get((normalize_name(name), team or ''))
    if cached:
        return cached
    norm = normalize_name(name)
    proj_name = None
    for key, proj in (fg_proj or {}).items():
        if normalize_name(proj.get('name') or '') == norm and (not team or proj.get('team') == team):
            proj_name = proj.get('name')
            break
    proj_name = proj_name or name
    match = (espn_matches or {}).get(proj_name) or (espn_matches or {}).get(name)
    if not match:
        for match_name, match_info in (espn_matches or {}).items():
            if normalize_name(match_name) == norm:
                match = match_info
                break
    if match and roster_map:
        info = roster_map.get(match.get('espn_id'))
        if info:
            return 'MY ROSTER' if info.get('team_id') == ESPN_TEAM_ID else 'OTHER'
    return 'FA'


def _projection_for_probable_game(game, fg_proj):
    pitcher_name = game.get('pitcher_name')
    pitcher_team = game.get('pitcher_team')
    if not pitcher_name:
        return None, None, 'no pitcher after probable validation'
    fg_by_name = {}
    for key, proj in (fg_proj or {}).items():
        fg_by_name[key] = proj
        name_only = key.split('|')[0]
        if name_only not in fg_by_name:
            fg_by_name[name_only] = proj
    norm_name = normalize_name(pitcher_name)
    norm_key = f"{norm_name}|{pitcher_team}"
    proj = fg_by_name.get(norm_key)
    if proj:
        return proj, norm_key, 'matched by normalized name + team'
    proj = fg_by_name.get(norm_name)
    if proj:
        return proj, norm_name, 'matched by normalized name fallback'
    return None, norm_key, 'no FanGraphs pitcher projection matched'


def _pipeline_status_for_probable_game(game, fg_proj=None, espn_matches=None, roster_map=None):
    out = {
        'projection_matched': False,
        'projection_key': None,
        'projection_reason': None,
        'scoring_row_built': False,
        'included_streaming': False,
        'included_today_decisions': False,
        'status': '',
        'tier': None,
        'projected_points': None,
        'reason': None,
    }
    if not game.get('pitcher_name'):
        out['reason'] = game.get('probable_note') or 'TBD/problem after probable-date validation'
        out['status'] = ''
        return out

    proj, proj_key, proj_reason = _projection_for_probable_game(game, fg_proj or {})
    out['projection_key'] = proj_key
    out['projection_reason'] = proj_reason
    if not proj:
        out['reason'] = 'dropped before scoring: no FanGraphs projection match'
        return out

    out['projection_matched'] = True
    out['projection_name'] = proj.get('name')
    out['projection_team'] = proj.get('team')
    out['proj_gs'] = proj.get('GS')
    out['proj_ip'] = proj.get('IP')
    status = _status_for_probable_pitcher(
        proj.get('name') or game.get('pitcher_name'),
        game.get('pitcher_team'),
        fg_proj,
        espn_matches,
        roster_map,
    )
    out['status'] = status
    sanity = projection_sanity_status(
        proj,
        probable_source=game.get('probable_source'),
        roster_status=status,
    )
    out['projection_sanity_status'] = sanity.get('status')
    out['projection_sanity_note'] = sanity.get('note')
    out['proj_ip_per_gs'] = sanity.get('original_ip_per_gs')
    out['proj_adjusted_ip_per_gs'] = sanity.get('adjusted_ip_per_gs')
    if sanity.get('status') == 'dropped':
        out['reason'] = f"dropped before scoring: {sanity.get('note')}"
        return out

    out['scoring_row_built'] = True

    try:
        # Approximate enough for diagnostics; the full tracker computes matchup
        # and learned adjustments separately. This command must not alter model
        # behavior or force a row into the report.
        out['projected_points'] = round(compute_pts_per_start(proj), 1)
        out['tier'] = classify_tier(out['projected_points'])
    except Exception:
        out['projected_points'] = None
        out['tier'] = None

    if status in ('FA', 'MY ROSTER', 'WAIVER'):
        out['included_streaming'] = True
        if (game.get('date') or '') == date.today().isoformat():
            out['included_today_decisions'] = True
        out['reason'] = 'included in report action pool'
    elif status:
        out['reason'] = f"hidden from report action pool: roster status is {status}"
    else:
        out['reason'] = 'hidden from report action pool: roster status is blank/unknown'
    return out


def explain_pitcher_schedule(pitcher_name):
    """Read-only diagnostic for current streaming-window probable-date handling."""
    global PREVIEW_LOCAL
    old_preview = PREVIEW_LOCAL
    PREVIEW_LOCAL = True
    try:
        target_norm = normalize_name(pitcher_name or '')
        week_start, week_end = get_streaming_window()
        print("PITCHER SCHEDULE EXPLANATION")
        print("=" * 60)
        print(f"Pitcher: {pitcher_name}")
        print(f"Streaming window: {week_start} to {week_end}")

        fg_proj = fetch_fg_pitcher_projections()
        schedule = fetch_weekly_schedule(week_start, week_end)
        espn_probables = fetch_espn_probables(week_start, week_end)

        espn_matches = {}
        roster_map = {}
        try:
            espn_players = fetch_espn_players()
            fg_players = [
                {'name': p.get('name'), 'team': p.get('team'), 'positions': ['P'], 'type': 'pitcher'}
                for p in (fg_proj or {}).values()
            ]
            espn_matches, _ = match_fg_to_espn(fg_players, espn_players)
            roster_map = fetch_espn_rosters(load_config()) or {}
            espn_matches = reconcile_with_roster(espn_matches, roster_map, espn_players)
        except Exception as e:
            print(f"Roster/status lookup warning: {e}")

        my_sps_by_team = _my_starting_pitchers_by_team(fg_proj, roster_map, espn_matches)
        resolved = _resolve_probable_schedule(schedule, espn_probables, my_sps_by_team)

        pitcher_ids_by_name = {}
        for game in resolved:
            name = game.get('pitcher_name')
            mid = game.get('pitcher_mlb_id')
            if name and mid:
                pitcher_ids_by_name[normalize_name(name)] = mid
        pitcher_ids_by_name = augment_workload_pitcher_ids(
            pitcher_ids_by_name,
            fg_proj,
            espn_probables=espn_probables,
            roster_map=roster_map,
            espn_matches=espn_matches,
        )
        workload = compute_pitcher_workload(PREDICTIONS_DIR, OUTCOMES_LOG, pitcher_ids_by_name)

        recent_dates = [
            (date.today() - timedelta(days=offset)).isoformat()
            for offset in range(0, 4)
        ]
        recent_completed = [
            (d, fetch_completed_starts_for_date(d, verbose=False))
            for d in recent_dates
        ]
        mixed_recent = _merge_recent_start_maps(
            _recent_actual_starts_from_outcomes(OUTCOMES_LOG),
            _recent_logged_start_evidence_from_outcomes(OUTCOMES_LOG, recent_dates),
            _recent_completed_starts_map(*recent_completed),
            _recent_prediction_start_evidence(recent_dates),
        )
        hard_recent, soft_recent = _split_recent_start_evidence(mixed_recent)
        workload_hard, workload_soft = _split_recent_start_evidence(_recent_actual_starts_from_workload(workload))
        hard_recent = _merge_recent_start_maps(hard_recent, workload_hard)
        soft_recent = _merge_recent_start_maps(soft_recent, workload_soft)

        validated, report = _validate_probable_schedule(
            resolved,
            recent_completed_starts=mixed_recent,
            pitcher_workload=workload,
            verbose=False,
            example_limit=20,
        )

        candidates = [
            g for g in resolved
            if normalize_name(g.get('pitcher_name') or '') == target_norm
        ]
        final_rows = [
            g for g in validated
            if normalize_name(g.get('pitcher_name') or g.get('probable_conflict_pitcher') or '') == target_norm
        ]

        print("\nSchedule/probable candidates")
        if not candidates:
            print("  None found in current fetched schedule/probable data.")
        pipeline_by_key = {}
        for game in candidates:
            key = _probable_assignment_id(game)
            pipeline = _pipeline_status_for_probable_game(game, fg_proj, espn_matches, roster_map)
            pipeline_by_key[key] = pipeline
            decision = 'kept'
            if key in report.get('suppressed', {}):
                decision = 'TBD/problem'
            elif key in report.get('warnings', {}):
                decision = 'kept with warning'
            status = pipeline.get('status') or _status_for_probable_pitcher(
                game.get('pitcher_name'), game.get('pitcher_team'), fg_proj, espn_matches, roster_map
            )
            validation_allows_display = decision in ('kept', 'kept with warning')
            included_streaming = bool(pipeline.get('included_streaming') and validation_allows_display)
            included_today = bool(pipeline.get('included_today_decisions') and validation_allows_display)
            if validation_allows_display:
                if included_streaming and decision == 'kept with warning':
                    visibility = 'included in Streaming with warning'
                elif included_streaming:
                    visibility = 'included in Streaming'
                else:
                    visibility = 'excluded after validation'
            else:
                visibility = decision
            hard = _recent_start_before_date(target_norm, game.get('date'), hard_recent)
            soft = _recent_start_before_date(target_norm, game.get('date'), soft_recent)
            print(
                f"  - {game.get('date')} {game.get('pitcher_team')} "
                f"{'vs' if game.get('home_away') == 'H' else 'at'} {game.get('opponent')} "
                f"| source={game.get('probable_source') or 'unknown'} | status={status} | {visibility}"
            )
            if key in report.get('suppressed', {}):
                print(f"      validation: {report['suppressed'][key]}")
            elif key in report.get('warnings', {}):
                print(f"      validation: {report['warnings'][key]}")
            else:
                print("      validation: no rest/date conflict")
            if hard:
                print(f"      hard evidence: {hard.get('date')} from {hard.get('source')}")
            else:
                print("      hard evidence: none before this date")
            if soft:
                print(f"      soft evidence: {soft.get('date')} from {soft.get('source')}")
            else:
                print("      soft evidence: none before this date")
            print(
                "      projection matched: "
                f"{'yes' if pipeline.get('projection_matched') else 'no'}"
                f" ({pipeline.get('projection_reason')})"
            )
            if pipeline.get('projection_matched'):
                print(
                    "      projection row: "
                    f"{pipeline.get('projection_name')} {pipeline.get('projection_team')} "
                    f"GS={pipeline.get('proj_gs')} IP={pipeline.get('proj_ip')} "
                    f"IP/GS={pipeline.get('proj_ip_per_gs')}"
                )
                sanity_text = pipeline.get('projection_sanity_status') or 'unknown'
                adjusted = pipeline.get('proj_adjusted_ip_per_gs')
                if adjusted is not None and adjusted != pipeline.get('proj_ip_per_gs'):
                    sanity_text += f" (adjusted IP/GS={adjusted})"
                if pipeline.get('projection_sanity_note'):
                    sanity_text += f" — {pipeline.get('projection_sanity_note')}"
                print(f"      projection sanity: {sanity_text}")
            print(f"      scoring row built: {'yes' if pipeline.get('scoring_row_built') else 'no'}")
            if pipeline.get('scoring_row_built'):
                pts_text = (
                    f"{pipeline.get('projected_points')} pts"
                    if pipeline.get('projected_points') is not None else 'points unavailable'
                )
                print(f"      final status/tier: {pipeline.get('status') or '?'} / {pipeline.get('tier') or '?'} / {pts_text}")
            print(f"      included in full Streaming list: {'yes' if included_streaming else 'no'}")
            print(f"      included in Today's Pitching Decisions: {'yes' if included_today else 'no'}")
            if not validation_allows_display:
                final_reason = report.get('suppressed', {}).get(key) or pipeline.get('reason')
            elif included_streaming and key in report.get('warnings', {}):
                final_reason = f"included with warning: {report['warnings'][key]}"
            else:
                final_reason = pipeline.get('reason')
            print(f"      final report reason: {final_reason}")

        print("\nFinal displayed date(s)")
        display_rows = []
        for game in final_rows:
            key = _probable_assignment_id(game)
            pipeline = pipeline_by_key.get(key)
            if game.get('pitcher_name') and pipeline and not pipeline.get('included_streaming'):
                continue
            display_rows.append(game)
        if not display_rows:
            print("  None.")
        for game in display_rows:
            if game.get('pitcher_name'):
                print(
                    f"  - {game.get('date')} {game.get('pitcher_team')} "
                    f"{'vs' if game.get('home_away') == 'H' else 'at'} {game.get('opponent')} "
                    f"| source={game.get('probable_source') or 'unknown'}"
                )
                if game.get('probable_warning'):
                    print(f"      warning: {game.get('probable_warning')}")
            else:
                print(
                    f"  - {game.get('date')} {game.get('pitcher_team')} "
                    f"{'vs' if game.get('home_away') == 'H' else 'at'} {game.get('opponent')} "
                    f"| TBD/problem for {game.get('probable_conflict_pitcher')}: {game.get('probable_note')}"
                )
        return {
            'candidates': len(candidates),
            'final_rows': len(final_rows),
            'suppressed': sum(1 for g in candidates if _probable_assignment_id(g) in report.get('suppressed', {})),
        }
    finally:
        PREVIEW_LOCAL = old_preview


def decision_summary_for_report(summary):
    if not summary:
        return None
    return {
        'date': summary.get('date'),
        'source': summary.get('source'),
        'rows_scanned': summary.get('rows_scanned', 0),
        'original_actionable': summary.get('original_actionable', 0),
        'actionable_count': summary.get('actionable_count', 0),
        'roster_count': summary.get('roster_count', 0),
        'fa_count': summary.get('fa_count', 0),
        'waiver_count': summary.get('waiver_count', 0),
        'hidden_other_count': summary.get('hidden_other_count', 0),
        'hidden_unknown_count': summary.get('hidden_unknown_count', 0),
        'roster_enriched_count': summary.get('enrichment', {}).get('roster_enriched_count', 0),
        'prediction_enriched_count': summary.get('enrichment', {}).get('prediction_enriched_count', 0),
        'roster_status_cache_rows': summary.get('enrichment', {}).get('roster_status_cache_rows', 0),
        'prediction_status_cache_rows': summary.get('enrichment', {}).get('prediction_status_cache_rows', 0),
        'status_unreliable': summary.get('status_unreliable', False),
        'warning': summary.get('warning'),
        'sections': {
            'best_available': _best_available_for_report(summary.get('fa_ranked', []), limit=6),
            'my_roster': [_decision_report_item(r) for r in summary.get('roster_ranked', [])[:6]],
            'risky_roster': _risky_roster_for_report(summary.get('risky_roster', []), limit=6),
            'avoid_traps': [_decision_report_item(r) for r in summary.get('avoid_traps', [])[:6]],
        },
        'problems': (summary.get('problems') or [])[:6],
    }


def build_next_watchlist_summary(base_date=None, records=None, source=None, days=3):
    """Build a report-only watchlist for upcoming actionable starts."""
    base_date = base_date or date.today().isoformat()
    try:
        start = date.fromisoformat(base_date) + timedelta(days=1)
    except Exception:
        start = date.today() + timedelta(days=1)
    watch_dates = [(start + timedelta(days=i)).isoformat() for i in range(days)]
    if records is None:
        source = source or 'prediction logs'
        records = []
        for d in watch_dates:
            rows, _ = _latest_prediction_records_by_date(d)
            records.extend(rows)
    else:
        records = [dict(r) for r in records]

    records = [
        r for r in records
        if (r.get('date') or r.get('game_date')) in set(watch_dates)
    ]
    records, probable_report = validate_probable_prediction_records(records, source=source or 'prediction records')
    records = [apply_visible_risk_guard_overlay(dict(r)) for r in records]
    summary = {
        'base_date': base_date,
        'date_range': f"{watch_dates[0]} to {watch_dates[-1]}" if watch_dates else '',
        'source': source or 'current report prediction records',
        'rows_scanned': len(records),
        'actionable_count': 0,
        'hidden_other_count': 0,
        'hidden_unknown_count': 0,
        'days': [],
        'problems': [],
        'probable_sanity': probable_report,
    }
    if not records:
        summary['problems'].append('No upcoming prediction records found for the next 3 days.')
        return summary

    actionable_statuses = {'FA', 'MY ROSTER', 'WAIVER'}
    records, enrichment = _enrich_decision_statuses(records)
    actionable = [r for r in records if r.get('status') in actionable_statuses]
    hidden_unknown = [r for r in records if not r.get('status')]
    hidden_other = [r for r in records if r.get('status') and r.get('status') not in actionable_statuses]
    summary['actionable_count'] = len(actionable)
    summary['hidden_other_count'] = len(hidden_other)
    summary['hidden_unknown_count'] = len(hidden_unknown)
    if hidden_unknown:
        summary['problems'].append(f"{len(hidden_unknown)} upcoming rows have blank roster/FA status and are hidden from the watchlist.")
    if hidden_other:
        summary['problems'].append(f"{len(hidden_other)} upcoming rows appear rostered by other teams/OTHER and are hidden.")
    summary['roster_enriched_count'] = enrichment.get('roster_enriched_count', 0)
    summary['prediction_enriched_count'] = enrichment.get('prediction_enriched_count', 0)

    for d in watch_dates:
        day_rows = [r for r in actionable if (r.get('date') or r.get('game_date')) == d]
        available = [
            r for r in day_rows
            if r.get('status') in ('FA', 'WAIVER')
        ]
        roster = [r for r in day_rows if r.get('status') == 'MY ROSTER']
        ranked_available = sorted(
            available,
            key=lambda r: (TIER_ORDER.get(r.get('tier', 'avoid'), 3), -_decision_points(r))
        )
        non_avoid_available = [r for r in ranked_available if r.get('tier') != 'avoid']
        best_available = (non_avoid_available[:4] if non_avoid_available else ranked_available[:3])
        risky_roster = sorted(
            [r for r in roster if r.get('tier') in ('borderline', 'avoid') or _decision_risk_boost_flags(r)[0]],
            key=lambda r: (TIER_ORDER.get(r.get('tier', 'avoid'), 3), _decision_points(r))
        )[:4]
        selected_keys = {
            (
                normalize_name(r.get('name') or r.get('pitcher_name') or ''),
                r.get('team'), r.get('opponent'), r.get('home_away')
            )
            for r in best_available + risky_roster
        }
        strong_starts = []
        for r in sorted(day_rows, key=lambda rec: -_decision_points(rec)):
            key = (
                normalize_name(r.get('name') or r.get('pitcher_name') or ''),
                r.get('team'), r.get('opponent'), r.get('home_away')
            )
            if key in selected_keys:
                continue
            if r.get('tier') in ('must_start', 'start') and _decision_points(r) >= 10:
                strong_starts.append(r)
            if len(strong_starts) >= 3:
                break

        day_items = []
        for label, rows in (
            ('FA/WAIVER TARGET', best_available),
            ('ROSTER RISK', risky_roster),
            ('PLAN AROUND', strong_starts),
        ):
            for rec in rows:
                item = _decision_report_item(rec)
                if label == 'FA/WAIVER TARGET' and rec.get('tier') == 'avoid':
                    item['watch_label'] = 'DESPERATION ONLY'
                elif label == 'FA/WAIVER TARGET' and item.get('risk_guard_candidate'):
                    item['watch_label'] = 'VOLUME ONLY'
                else:
                    item['watch_label'] = label
                day_items.append(item)

        if day_items:
            try:
                date_label = datetime.strptime(d, '%Y-%m-%d').strftime('%a %b %-d')
            except Exception:
                date_label = d
            summary['days'].append({
                'date': d,
                'label': date_label,
                'items': day_items[:8],
            })
    if not summary['days']:
        summary['problems'].append('No actionable upcoming starts matched the watchlist rules.')
    if summary.get('probable_sanity', {}).get('suppressed_total'):
        summary['problems'].append(
            f"{summary['probable_sanity']['suppressed_total']} low-confidence probable date(s) were moved to problem/TBD status."
        )
    return summary


def _action_matchup_text(item):
    if item.get('home_away') == 'H':
        return f"vs {item.get('opponent') or '?'}"
    if item.get('home_away') == 'A':
        return f"at {item.get('opponent') or '?'}"
    return f"vs {item.get('opponent') or '?'}"


def _action_date_text(date_value, base_date):
    if not date_value or date_value == base_date:
        return 'today'
    try:
        delta = (date.fromisoformat(date_value) - date.fromisoformat(base_date)).days
    except Exception:
        delta = None
    if delta == 1:
        return 'tomorrow'
    try:
        return datetime.strptime(date_value, '%Y-%m-%d').strftime('%a')
    except Exception:
        return date_value


def _action_item(kind, text, item, date_value, base_date, priority):
    return {
        'kind': kind,
        'text': _compact_decision_text(text, 120),
        'date': date_value,
        'date_label': _action_date_text(date_value, base_date),
        'name': item.get('name'),
        'team': item.get('team'),
        'opponent': item.get('opponent'),
        'home_away': item.get('home_away'),
        'status': item.get('status'),
        'points': item.get('points'),
        'confidence': item.get('confidence'),
        'priority': priority,
    }


def build_add_drop_priority_summary(base_date, daily_summary=None, watchlist_summary=None):
    """Create a short, conservative action list from existing report summaries."""
    actions = []
    seen = set()

    def add_action(kind, text, item, date_value, priority):
        key = (
            kind,
            date_value,
            normalize_name(item.get('name') or ''),
            item.get('team'),
            item.get('opponent'),
        )
        if key in seen:
            return
        seen.add(key)
        actions.append(_action_item(kind, text, item, date_value, base_date, priority))

    daily_sections = (daily_summary or {}).get('sections') or {}
    for item in daily_sections.get('best_available', [])[:3]:
        matchup = _action_matchup_text(item)
        pts = item.get('points') or 0
        if item.get('tier') in ('must_start', 'start'):
            text = f"Add {item.get('name')} for today against {item.get('opponent')} ({pts:.1f} pts) if available."
            add_action('ADD', text, item, (daily_summary or {}).get('date') or base_date, 10)
        elif item.get('tier') == 'borderline':
            if item.get('risk_guard_candidate'):
                text = f"Avoid {item.get('name')} unless chasing volume today {matchup} ({pts:.1f} pts); backtest flags extra bust risk."
                add_action('CAUTION', text, item, (daily_summary or {}).get('date') or base_date, 35)
            else:
                text = f"Consider {item.get('name')} only if you need volume today {matchup} ({pts:.1f} pts); playable but not safe."
                add_action('CONSIDER', text, item, (daily_summary or {}).get('date') or base_date, 30)
        else:
            text = f"Desperation only: {item.get('name')} today {matchup} ({pts:.1f} pts)."
            add_action('DESPERATION', text, item, (daily_summary or {}).get('date') or base_date, 80)

    for day in (watchlist_summary or {}).get('days', []):
        day_date = day.get('date')
        for item in day.get('items', []):
            label = item.get('watch_label')
            if label not in ('FA/WAIVER TARGET', 'VOLUME ONLY', 'DESPERATION ONLY'):
                continue
            pts = item.get('points') or 0
            date_text = _action_date_text(day_date, base_date)
            matchup = _action_matchup_text(item)
            if label == 'DESPERATION ONLY' or item.get('tier') == 'avoid':
                text = f"Desperation only: {item.get('name')} {date_text} {matchup} ({pts:.1f} pts)."
                add_action('DESPERATION', text, item, day_date, 85)
            elif item.get('tier') in ('must_start', 'start'):
                text = f"Add or queue {item.get('name')} for {date_text} {matchup} ({pts:.1f} pts)."
                add_action('ADD', text, item, day_date, 20)
            elif label == 'VOLUME ONLY' or item.get('risk_guard_candidate'):
                text = f"Watch only as a volume fallback: {item.get('name')} {date_text} {matchup} ({pts:.1f} pts); risk-guard profile."
                add_action('WATCH', text, item, day_date, 55)
            else:
                text = f"Watch {item.get('name')} for {date_text}; borderline stream, not a priority add {matchup} ({pts:.1f} pts)."
                add_action('WATCH', text, item, day_date, 45)

    for item in daily_sections.get('risky_roster', [])[:4]:
        pts = item.get('points') or 0
        matchup = _action_matchup_text(item)
        if item.get('tier') == 'avoid':
            text = f"Bench {item.get('name')} unless desperate today {matchup} ({pts:.1f} pts)."
            add_action('BENCH', text, item, (daily_summary or {}).get('date') or base_date, 25)
        elif item.get('tier') == 'borderline':
            text = f"Be careful with {item.get('name')} today {matchup}; playable but not safe ({pts:.1f} pts)."
            add_action('CAUTION', text, item, (daily_summary or {}).get('date') or base_date, 50)
        elif item.get('risks'):
            text = f"Check risk on {item.get('name')} today {matchup} before locking him in ({pts:.1f} pts)."
            add_action('CAUTION', text, item, (daily_summary or {}).get('date') or base_date, 55)

    for item in daily_sections.get('avoid_traps', [])[:3]:
        pts = item.get('points') or 0
        text = f"Avoid {item.get('name')} today despite name value ({pts:.1f} pts vs {item.get('opponent') or '?'})."
        add_action('AVOID', text, item, (daily_summary or {}).get('date') or base_date, 70)

    actions = sorted(actions, key=lambda a: (a.get('priority', 99), a.get('date') or '', a.get('name') or ''))[:8]
    return {
        'date': base_date,
        'items': actions,
        'count': len(actions),
    }


def _matchup_action(kind, text, priority, source='matchup', meta=None):
    return {
        'kind': kind,
        'text': _compact_decision_text(text, 220),
        'priority': priority,
        'source': source,
        'meta': meta or {},
    }


def _matchup_action_label_priority(kind):
    return {
        'LOCK IN': 0,
        'ADD': 10,
        'CONSIDER': 30,
        'BENCH': 40,
        'WATCH': 60,
        'AVOID': 80,
    }.get(kind, 99)


def _matchup_player_is_pitcher(row):
    values = {str(row.get('slot') or ''), str(row.get('pos') or '')}
    return bool(values & {'P', 'SP', 'RP'})


def _matchup_player_is_hitter(row):
    return bool(row.get('name')) and not _matchup_player_is_pitcher(row) and row.get('slot_id') not in ESPN_INJURY_SLOT_IDS


def _matchup_today_team_set(records, target_date=None):
    target_date = target_date or date.today().isoformat()
    teams = set()
    for rec in records or []:
        if (rec.get('date') or rec.get('game_date')) != target_date:
            continue
        if rec.get('team'):
            teams.add(rec.get('team'))
        if rec.get('opponent'):
            teams.add(rec.get('opponent'))
    return teams


def _matchup_decision_item_text(prefix, item, date_label='today'):
    matchup = _action_matchup_text(item)
    pts = item.get('points') or 0
    return f"{prefix} {item.get('name')} {date_label} {matchup} ({pts:.1f} pts, {item.get('confidence') or item.get('tier')})."


def _matchup_window_dates(base_date=None, days=3):
    try:
        start = date.fromisoformat(base_date or date.today().isoformat())
    except Exception:
        start = date.today()
    return [(start + timedelta(days=offset)).isoformat() for offset in range(days + 1)]


def _matchup_action_source_kind(source):
    source = str(source or '').lower()
    if 'current' in source:
        return 'current_run'
    if 'fast' in source or 'cached' in source or 'prediction log' in source:
        return 'prediction_log_cache'
    return 'prediction_log_cache'


def _matchup_record_date(record):
    return record.get('date') or record.get('game_date')


def _matchup_record_snapshot_date(record):
    value = record.get('logged_at') or record.get('snapshot_time')
    if isinstance(value, str) and len(value) >= 10:
        return value[:10]
    return None


def _matchup_projection_records(base_date=None, days=3):
    """Read existing prediction logs for today through the next N days."""
    records = []
    for target in _matchup_window_dates(base_date, days):
        rows, _ = _latest_prediction_records_by_date(target)
        for rec in rows:
            rec = dict(rec)
            rec['_matchup_source'] = 'prediction_log_cache'
            rec['_matchup_snapshot_date'] = _matchup_record_snapshot_date(rec)
            records.append(apply_visible_risk_guard_overlay(rec))
    return records


def _matchup_prediction_records_for_actions(base_date=None, days=3, records=None, source=None):
    """Choose the freshest prediction records available for matchup actions."""
    if records:
        allowed_dates = set(_matchup_window_dates(base_date, days))
        source_kind = _matchup_action_source_kind(source or 'current run prediction records')
        out = []
        for rec in records:
            rec = dict(rec)
            game_date = _matchup_record_date(rec)
            if game_date not in allowed_dates:
                continue
            rec['_matchup_source'] = source_kind
            rec['_matchup_snapshot_date'] = _matchup_record_snapshot_date(rec) or base_date
            out.append(apply_visible_risk_guard_overlay(rec))
        if out:
            return out, source_kind, source or 'current_run'
    return _matchup_projection_records(base_date, days), 'prediction_log_cache', 'prediction_log_cache'


def _matchup_projection_lookup(records):
    lookup = {}
    for rec in records or []:
        name = normalize_name(rec.get('name') or rec.get('pitcher_name') or '')
        if not name:
            continue
        lookup.setdefault(name, []).append(rec)
    for rows in lookup.values():
        rows.sort(key=lambda r: (_matchup_record_date(r) or '', -(float(_decision_points(r) or 0))))
    return lookup


def _matchup_projection_conflict(projections):
    assignments = {
        (
            _matchup_record_date(rec),
            rec.get('opponent'),
            rec.get('home_away'),
        )
        for rec in projections or []
    }
    assignments.discard((None, None, None))
    return len(assignments) > 1, sorted(assignments)


def _matchup_projection_context(record):
    game_date = _matchup_record_date(record) or 'unknown date'
    opponent = record.get('opponent') or '?'
    home_away = record.get('home_away') or '?'
    matchup = f"vs {opponent}" if home_away == 'H' else f"at {opponent}" if home_away == 'A' else f"{home_away} {opponent}"
    return f"{game_date} {matchup}, {_decision_points(record):.1f} pts, {record.get('tier') or 'unknown'}"


def _matchup_action_meta(source_kind, game_date=None, opponent=None, snapshot_date=None, note=None):
    return {
        'source': source_kind or 'prediction_log_cache',
        'game_date': game_date,
        'opponent': opponent,
        'snapshot_date': snapshot_date,
        'note': note,
    }


def build_matchup_action_recommendations(snapshot=None, base_date=None, limit=10,
                                         prediction_records=None, prediction_source=None):
    """Read-only weekly matchup actions from ESPN snapshot + existing predictions."""
    base_date = base_date or date.today().isoformat()
    snapshot = snapshot or build_matchup_snapshot()
    actions = []
    seen = set()
    notes = []
    seen_pitcher_action_dates = {}

    def add(kind, text, priority=None, source='matchup', meta=None):
        key = (kind, _compact_decision_text(text, 120))
        if key in seen:
            return
        seen.add(key)
        actions.append(_matchup_action(
            kind,
            text,
            _matchup_action_label_priority(kind) if priority is None else priority,
            source=source,
            meta=meta,
        ))

    def add_prediction_action(kind, text, item, game_date, priority, source_kind, source='prediction_log'):
        name_key = normalize_name(item.get('name') or item.get('pitcher_name') or '')
        prior_date = seen_pitcher_action_dates.get(name_key)
        if name_key and prior_date and game_date and prior_date != game_date:
            notes.append(
                f"{item.get('name') or item.get('pitcher_name')} has probable-date conflict "
                f"({prior_date} and {game_date}); using {prior_date}, verify manually."
            )
            return
        if name_key and game_date:
            seen_pitcher_action_dates[name_key] = game_date
        add(
            kind,
            text,
            priority,
            source,
            _matchup_action_meta(
                source_kind,
                game_date=game_date,
                opponent=item.get('opponent'),
                snapshot_date=item.get('_matchup_snapshot_date'),
            ),
        )

    if not snapshot or snapshot.get('low_confidence'):
        return {
            'date': base_date,
            'items': [],
            'count': 0,
            'notes': ['Matchup actions suppressed: unable to identify current ESPN matchup confidently.'],
        }
    if snapshot.get('error'):
        add('WATCH', f"Matchup snapshot unavailable: {(snapshot or {}).get('error') or 'unknown ESPN error'}.", 90)
        return {'date': base_date, 'items': actions, 'count': len(actions), 'notes': ['ESPN snapshot unavailable']}

    prediction_records, prediction_source_kind, prediction_source_label = _matchup_prediction_records_for_actions(
        base_date,
        days=3,
        records=prediction_records,
        source=prediction_source,
    )
    daily_raw = build_daily_decision_summary(
        base_date,
        records=prediction_records,
        source=prediction_source_label,
    )
    daily = decision_summary_for_report(daily_raw)
    watchlist = build_next_watchlist_summary(
        base_date,
        records=prediction_records,
        source=prediction_source_label,
    )
    projection_lookup = _matchup_projection_lookup(prediction_records)

    for slot in (snapshot.get('empty_slots') or {}).get('mine') or []:
        add(
            'LOCK IN',
            f"Fill empty active lineup slot {slot} if ESPN still shows it open.",
            1,
            'espn_matchup',
            _matchup_action_meta('current_run', game_date=base_date),
        )

    active_injured = [
        row for row in snapshot.get('my_active') or []
        if row.get('injury') and row.get('slot_id') not in ESPN_INJURY_SLOT_IDS
    ]
    injured_active_names = {normalize_name(row.get('name') or '') for row in active_injured if row.get('name')}
    for row in active_injured[:3]:
        name_key = normalize_name(row.get('name') or '')
        projections = projection_lookup.get(name_key) or []
        if projections:
            context = _matchup_projection_context(projections[0])
            projection_source = projections[0].get('_matchup_source') or prediction_source_kind
            conflict, assignments = _matchup_projection_conflict(projections)
            conflict_note = ''
            if conflict:
                compact = ', '.join(
                    f"{d} {ha or ''}{opp or ''}".strip()
                    for d, opp, ha in assignments[:3]
                )
                conflict_note = f" Probable-date conflict ({compact}); verify manually."
                notes.append(f"{row.get('name')} has multiple projected dates in {projection_source}; verify manually.")
            if projection_source == 'current_run':
                conflict_text = 'conflicts with current projection/start data'
            else:
                conflict_text = 'has cached projection data'
            add(
                'WATCH',
                (
                    f"{row.get('name')} in active slot {row.get('slot')}: ESPN injury status "
                    f"{row.get('injury')} {conflict_text} ({context}). "
                    f"Verify manually before locking lineup.{conflict_note}"
                ),
                4,
                'espn_roster+projection',
                _matchup_action_meta(
                    projection_source,
                    game_date=_matchup_record_date(projections[0]),
                    opponent=projections[0].get('opponent'),
                    snapshot_date=projections[0].get('_matchup_snapshot_date'),
                    note='probable-date conflict' if conflict else None,
                ),
            )
        else:
            add(
                'BENCH',
                (
                    f"Check {row.get('name')} in active slot {row.get('slot')}: ESPN injury status "
                    f"is {row.get('injury')}; no current projection/start data found."
                ),
                5 if str(row.get('injury')).upper() in ('OUT', 'FIFTEEN_DAY_DL', 'TEN_DAY_DL') else 35,
                'espn_roster',
                _matchup_action_meta('current_run', game_date=base_date),
            )

    today_teams = _matchup_today_team_set(prediction_records, base_date)
    if today_teams:
        active_hitters_without_game = [
            row for row in snapshot.get('my_active') or []
            if _matchup_player_is_hitter(row) and row.get('team') and row.get('team') not in today_teams
        ]
        bench_hitters_with_game = [
            row for row in snapshot.get('my_bench') or []
            if _matchup_player_is_hitter(row) and row.get('team') in today_teams and not row.get('injury')
        ]
        for active in active_hitters_without_game[:2]:
            if not bench_hitters_with_game:
                break
            bench = bench_hitters_with_game[0]
            add(
                'CONSIDER',
                f"Check hitter volume: {active.get('name')} appears active with no game today; {bench.get('name')} has a game if eligible.",
                28,
                'espn_roster',
                _matchup_action_meta(prediction_source_kind, game_date=base_date),
            )

    sections = (daily or {}).get('sections') or {}
    for item in sections.get('my_roster', [])[:4]:
        if normalize_name(item.get('name') or '') in injured_active_names:
            continue
        if item.get('tier') in ('must_start', 'start') and not item.get('risks'):
            add_prediction_action(
                'LOCK IN',
                _matchup_decision_item_text('Lock in', item),
                item,
                base_date,
                12,
                prediction_source_kind,
            )

    for item in sections.get('risky_roster', [])[:4]:
        if normalize_name(item.get('name') or '') in injured_active_names:
            continue
        if item.get('tier') == 'avoid':
            add_prediction_action('BENCH', _matchup_decision_item_text('Bench unless desperate:', item), item, base_date, 18, prediction_source_kind)
        elif item.get('tier') == 'borderline':
            prefix = 'Verify as volume-only fallback:' if item.get('risk_guard_candidate') else 'Use only if you need volume:'
            add_prediction_action('WATCH', _matchup_decision_item_text(prefix, item), item, base_date, 38, prediction_source_kind)
        else:
            risk = (item.get('risks') or ['risk flags'])[0]
            add_prediction_action('CONSIDER', f"Check {item.get('name')} before lock: {risk}.", item, base_date, 42, prediction_source_kind)

    for item in sections.get('best_available', [])[:4]:
        if item.get('tier') in ('must_start', 'start'):
            add_prediction_action('ADD', _matchup_decision_item_text('Add/start', item), item, base_date, 20, prediction_source_kind)
        elif item.get('tier') == 'borderline':
            if item.get('risk_guard_candidate'):
                add_prediction_action('WATCH', _matchup_decision_item_text('Avoid unless chasing volume:', item), item, base_date, 48, prediction_source_kind)
            else:
                add_prediction_action('CONSIDER', _matchup_decision_item_text('Consider only for volume:', item), item, base_date, 45, prediction_source_kind)

    for item in sections.get('avoid_traps', [])[:3]:
        add_prediction_action('AVOID', _matchup_decision_item_text('Avoid streaming', item), item, base_date, 70, prediction_source_kind)

    for day in (watchlist or {}).get('days', []):
        date_label = _action_date_text(day.get('date'), base_date)
        for item in day.get('items', [])[:4]:
            if item.get('status') not in ('FA', 'WAIVER'):
                continue
            if item.get('tier') in ('must_start', 'start'):
                add_prediction_action('WATCH', _matchup_decision_item_text('Queue streamer', item, date_label), item, day.get('date'), 55, prediction_source_kind)
            elif item.get('tier') == 'borderline':
                prefix = 'Watch only as risky volume fallback' if item.get('risk_guard_candidate') else 'Watch as volume fallback'
                add_prediction_action('WATCH', _matchup_decision_item_text(prefix, item, date_label), item, day.get('date'), 62, prediction_source_kind)
            if len(actions) >= limit + 4:
                break

    notes.insert(0, f"Pitcher start dates source: {prediction_source_kind}.")
    for label, summary_obj in (('today', daily_raw), ('next 3 days', watchlist)):
        suppressed = (summary_obj or {}).get('probable_sanity', {}).get('suppressed_total', 0)
        if suppressed:
            notes.append(f"{suppressed} low-confidence probable date(s) suppressed from {label} recommendations; verify manually.")
    if (daily or {}).get('status_unreliable'):
        notes.append('Roster/FA filtering may be stale; refresh with --preview-local if recommendations look sparse.')
    if not today_teams:
        notes.append('Could not infer MLB teams playing today from prediction records; hitter no-game checks were skipped.')
    if not actions:
        add('WATCH', 'No clear matchup action found from current snapshot and prediction logs.', 95)

    actions = sorted(actions, key=lambda a: (a.get('priority', 99), a.get('kind'), a.get('text')))[:limit]
    return {'date': base_date, 'items': actions, 'count': len(actions), 'notes': notes}


def print_matchup_actions(action_summary):
    print("\nMATCHUP ACTION RECOMMENDATIONS")
    print("=" * 60)
    print("Read-only: uses existing prediction logs, roster data, and matchup snapshot. No roster moves are made.")
    items = (action_summary or {}).get('items') or []
    if not items:
        print("  None")
    for idx, action in enumerate(items[:10], 1):
        meta = action.get('meta') or {}
        context = []
        if meta.get('source'):
            context.append(f"source={meta.get('source')}")
        if meta.get('game_date'):
            context.append(f"game_date={meta.get('game_date')}")
        if meta.get('opponent'):
            context.append(f"opp={meta.get('opponent')}")
        if meta.get('snapshot_date'):
            context.append(f"snapshot={meta.get('snapshot_date')}")
        if meta.get('note'):
            context.append(str(meta.get('note')))
        suffix = f" [{' | '.join(context)}]" if context else ""
        print(f"{idx:>2}. {action.get('kind')}: {action.get('text')}{suffix}")
    notes = (action_summary or {}).get('notes') or []
    if notes:
        print("\nNotes")
        for note in notes:
            print(f"  - {note}")


def matchup_actions():
    snapshot = build_matchup_snapshot()
    actions = build_matchup_action_recommendations(snapshot)
    print_matchup_actions(actions)
    return actions


def _hitter_player_rows(players_list):
    out = []
    for player in players_list or []:
        ptype = player.get('type')
        positions = set(player.get('positions') or [])
        display = player.get('displayPos') or player.get('best_pos') or ''
        if ptype == 'pitcher' or display in ('SP', 'RP', 'P') or positions == {'P'}:
            continue
        row = dict(player)
        row['_norm'] = normalize_name(row.get('name') or '')
        out.append(row)
    return out


def _hitter_lookup(players_list):
    lookup = {}
    for row in _hitter_player_rows(players_list):
        if row.get('_norm') and row['_norm'] not in lookup:
            lookup[row['_norm']] = row
    return lookup


def _hitter_value(row, lookup):
    player = lookup.get(normalize_name((row or {}).get('name') or '')) or {}
    return {
        'espn_id': player.get('espn_id'),
        'fg_id': player.get('fg_id'),
        'dollars': _safe_float(player.get('dollars')) or 0.0,
        'rpts': _safe_float(player.get('rpts')) or 0.0,
        'positions': player.get('positions') or [],
        'display_pos': player.get('displayPos') or player.get('best_pos') or row.get('pos') or '',
        'status': player.get('status') or '',
    }


def _hitter_team_has_game(row, today_teams):
    team = (row or {}).get('team')
    if not team or not today_teams:
        return None
    return team in today_teams


def _hitter_field(row, value, *keys):
    for source in (row or {}, value or {}):
        for key in keys:
            val = source.get(key)
            if val not in (None, ''):
                return val
    return None


def _normalize_hand_code(value):
    if value in (None, ''):
        return None
    text = str(value).strip().upper()
    if text in ('L', 'LEFT', 'LEFTY'):
        return 'L'
    if text in ('R', 'RIGHT', 'RIGHTY'):
        return 'R'
    if text in ('S', 'SWITCH', 'BOTH'):
        return 'S'
    return None


def _hitter_platoon_context(hitter_bats, pitcher_hand):
    """Simple read-only hitter platoon label; not used for recommendations."""
    bat = _normalize_hand_code(hitter_bats)
    hand = _normalize_hand_code(pitcher_hand)
    if not bat or not hand:
        return {
            'label': 'unknown',
            'note': 'platoon unknown',
            'detail': 'missing hitter bat side or opposing pitcher hand',
        }
    if bat == 'S':
        return {
            'label': 'switch_hitter',
            'note': f'switch hitter vs {hand}HP',
            'detail': 'switch hitter can usually take the preferred side',
        }
    if bat != hand:
        return {
            'label': 'platoon_edge',
            'note': f'platoon edge vs {hand}HP',
            'detail': 'opposite-side hitter matchup',
        }
    return {
        'label': 'platoon_risk',
        'note': f'platoon risk vs {hand}HP',
        'detail': 'same-side hitter matchup',
    }


def _handedness_player_lookup(team_handedness):
    lookup = {}
    for team, data in (team_handedness or {}).items():
        for norm, player in (data or {}).get('players', {}).items():
            if not norm:
                continue
            out = dict(player or {})
            out.setdefault('team', team)
            lookup.setdefault(norm, out)
    return lookup


def _hitter_batting_order_spot(value):
    if value in (None, ''):
        return None
    text = str(value).strip()
    if not text.isdigit():
        return None
    try:
        order = int(text)
    except ValueError:
        return None
    if order <= 0:
        return None
    return max(1, order // 100)


def _fetch_hitter_lineup_context(records, base_date=None, force_refresh=False):
    """Read posted MLB boxscore lineups for today's games when available."""
    base_date = base_date or date.today().isoformat()
    cache_name = f"hitter_lineup_context_{base_date}.json"
    cached, _age = _load_streaming_cache(cache_name, max_age_hours=1)
    if isinstance(cached, dict) and not force_refresh:
        return cached

    game_pks = sorted({
        rec.get('game_pk')
        for rec in records or []
        if _matchup_record_date(rec) == base_date and rec.get('game_pk')
    })
    if not game_pks:
        return {'date': base_date, 'players': {}, 'teams_with_posted_lineups': [], 'game_pks': []}

    def fetch_box(pk):
        try:
            r = requests.get(f"https://statsapi.mlb.com/api/v1/game/{pk}/boxscore", timeout=15)
            r.raise_for_status()
            return pk, r.json()
        except Exception:
            return pk, None

    players = {}
    teams_with_posted = set()
    with ThreadPoolExecutor(max_workers=8) as ex:
        for pk, box in ex.map(fetch_box, game_pks):
            if not box:
                continue
            for side in ('home', 'away'):
                team_info = (box.get('teams') or {}).get(side, {}) or {}
                team_id = (team_info.get('team') or {}).get('id')
                team_abbr = MLB_TEAM_TO_ABBR.get(team_id, '')
                raw_players = team_info.get('players') or {}
                team_has_order = any(p.get('battingOrder') for p in raw_players.values())
                if team_has_order and team_abbr:
                    teams_with_posted.add(team_abbr)
                for pinfo in raw_players.values():
                    person = pinfo.get('person') or {}
                    name = person.get('fullName') or ''
                    if not name:
                        continue
                    pos = (pinfo.get('position') or {}).get('abbreviation') or ''
                    if pos == 'P':
                        continue
                    batting_order = pinfo.get('battingOrder')
                    spot = _hitter_batting_order_spot(batting_order)
                    lineup_status = 'confirmed_starting' if spot is not None else (
                        'not_in_confirmed_lineup' if team_has_order else 'unknown'
                    )
                    players[normalize_name(name)] = {
                        'name': name,
                        'mlb_id': person.get('id'),
                        'team': team_abbr,
                        'game_pk': pk,
                        'lineup_status': lineup_status,
                        'batting_order_status': 'confirmed' if spot is not None else (
                            'posted_without_player' if team_has_order else 'unknown'
                        ),
                        'batting_order_spot': spot,
                        'batting_order_raw': batting_order,
                        'position': pos,
                    }

    payload = {
        'date': base_date,
        'source': 'MLB StatsAPI boxscore battingOrder',
        'refreshed_at': datetime.now().isoformat(timespec='seconds'),
        'players': players,
        'teams_with_posted_lineups': sorted(teams_with_posted),
        'game_pks': game_pks,
    }
    _save_streaming_cache(cache_name, payload)
    return payload


def _hitter_prediction_features(record):
    features = dict((record or {}).get('features') or {})
    for key in (
        'proj_era', 'proj_whip', 'proj_k9', 'xera', 'fip', 'xfip', 'siera',
        'hard_hit_pct', 'barrel_pct', 'whiff_pct', 'bb_pct_savant',
        'k_pct_savant', 'park_factor', 'park', 'venue_name', 'roof_type',
        'is_indoor_or_dome', 'weather_temp_f', 'weather_wind_speed_mph',
        'weather_source', 'weather_note', 'pitcher_hand',
    ):
        if features.get(key) in (None, '') and (record or {}).get(key) not in (None, ''):
            features[key] = record.get(key)
    return features


def _hitter_probable_context(record):
    features = _hitter_prediction_features(record)
    return {
        'game_pk': (record or {}).get('game_pk'),
        'game_datetime': (record or {}).get('game_datetime') or features.get('game_datetime'),
        'venue_name': (record or {}).get('venue_name') or features.get('venue_name'),
        'park': features.get('park'),
        'park_factor': _safe_float(features.get('park_factor')),
        'roof_type': features.get('roof_type'),
        'is_indoor_or_dome': features.get('is_indoor_or_dome'),
        'weather_source': features.get('weather_source'),
        'weather_temp_f': _safe_float(features.get('weather_temp_f')),
        'weather_wind_speed_mph': _safe_float(features.get('weather_wind_speed_mph')),
        'weather_note': features.get('weather_note'),
        'opposing_probable_pitcher_id': (record or {}).get('pitcher_id'),
        'opposing_pitcher_projected_pts': _safe_float(
            (record or {}).get('predicted_pts')
            if (record or {}).get('predicted_pts') is not None
            else (record or {}).get('pts')
        ),
        'opposing_pitcher_tier': (record or {}).get('tier'),
        'opposing_pitcher_hand': (
            (record or {}).get('pitcher_hand')
            or features.get('pitcher_hand')
            or features.get('throws')
        ),
        'opposing_pitcher_proj_era': _safe_float(features.get('proj_era')),
        'opposing_pitcher_proj_whip': _safe_float(features.get('proj_whip')),
        'opposing_pitcher_proj_k9': _safe_float(features.get('proj_k9')),
        'opposing_pitcher_xera': _safe_float(features.get('xera')),
        'opposing_pitcher_fip': _safe_float(features.get('fip')),
        'opposing_pitcher_xfip': _safe_float(features.get('xfip')),
        'opposing_pitcher_siera': _safe_float(features.get('siera')),
        'opposing_pitcher_hard_hit_pct': _safe_float(features.get('hard_hit_pct')),
        'opposing_pitcher_barrel_pct': _safe_float(features.get('barrel_pct')),
        'opposing_pitcher_whiff_pct': _safe_float(features.get('whiff_pct')),
        'opposing_pitcher_k_pct': _safe_float(features.get('k_pct_savant')),
        'opposing_pitcher_bb_pct': _safe_float(features.get('bb_pct_savant')),
    }


def _hitter_game_context_by_team(records, base_date=None, days=6):
    base_date = base_date or date.today().isoformat()
    allowed = set(_matchup_window_dates(base_date, days))
    by_team = defaultdict(list)
    for rec in records or []:
        game_date = _matchup_record_date(rec)
        if game_date not in allowed:
            continue
        pitcher_team = rec.get('team')
        opponent = rec.get('opponent')
        home_away = rec.get('home_away')
        pitcher_name = rec.get('name') or rec.get('pitcher_name')
        probable_context = _hitter_probable_context(rec)
        if pitcher_team:
            by_team[pitcher_team].append({
                'date': game_date,
                'opponent': opponent,
                'home_away': home_away,
                'probable_pitcher': pitcher_name,
                'probable_pitcher_id': rec.get('pitcher_id'),
                'probable_pitcher_team': pitcher_team,
                'probable_source': rec.get('probable_source'),
                'is_opposing_pitcher': False,
                **probable_context,
            })
        if opponent:
            hitter_home_away = 'A' if home_away == 'H' else 'H' if home_away == 'A' else ''
            by_team[opponent].append({
                'date': game_date,
                'opponent': pitcher_team,
                'home_away': hitter_home_away,
                'opposing_probable_pitcher': pitcher_name,
                'probable_pitcher_team': pitcher_team,
                'probable_source': rec.get('probable_source'),
                'is_opposing_pitcher': True,
                **probable_context,
            })
    for games in by_team.values():
        games.sort(key=lambda g: (g.get('date') or '', g.get('opponent') or '', g.get('probable_pitcher') or g.get('opposing_probable_pitcher') or ''))
    return by_team


def _hitter_context_row(row, lookup, game_context, base_date, roster_state,
                        team_handedness=None, lineup_context=None):
    value = _hitter_value(row, lookup)
    team = row.get('team') or ''
    games = game_context.get(team) or []
    today_games = [g for g in games if g.get('date') == base_date]
    today_game = next((g for g in today_games if g.get('is_opposing_pitcher')), today_games[0] if today_games else {})
    status = row.get('status') or value.get('status') or ''
    team_hand = (team_handedness or {}).get(team) or {}
    hand_player = _handedness_player_lookup(team_handedness).get(normalize_name(row.get('name') or '')) or {}
    lineup_player = ((lineup_context or {}).get('players') or {}).get(normalize_name(row.get('name') or '')) or {}
    hitter_bats = (
        _hitter_field(row, value, 'bats', 'bat_side', 'batSide', 'bat_hand')
        or hand_player.get('bat_side')
    )
    hitter_throws = (
        _hitter_field(row, value, 'throws', 'throw_side', 'throwHand')
        or hand_player.get('throws')
    )
    opp_hand = today_game.get('opposing_pitcher_hand')
    platoon_context = _hitter_platoon_context(hitter_bats, opp_hand)
    lineup_status = lineup_player.get('lineup_status') or 'unknown'
    batting_order_status = lineup_player.get('batting_order_status') or 'unknown'
    batting_order_spot = lineup_player.get('batting_order_spot')
    notes = []
    if not today_game and team:
        notes.append('no game found in current prediction window')
    if hitter_bats is None:
        notes.append('hitter handedness unavailable from current cached inputs')
    if opp_hand is None and today_game:
        notes.append('opposing pitcher handedness unavailable from current cached inputs')
    if lineup_status == 'unknown':
        notes.append('confirmed lineup not posted or unavailable from MLB boxscore yet')
    return {
        'date': base_date,
        'name': row.get('name') or '',
        'normalized_name': normalize_name(row.get('name') or ''),
        'team': team,
        'espn_id': row.get('espn_id') or value.get('espn_id'),
        'fg_id': row.get('fg_id') or value.get('fg_id'),
        'slot': row.get('slot') or '',
        'slot_id': row.get('slot_id'),
        'roster_state': roster_state,
        'roster_status': status,
        'injury_status': row.get('injury') or '',
        'positions': value.get('positions') or [],
        'display_pos': value.get('display_pos') or row.get('pos') or '',
        'hitter_bats': hitter_bats,
        'hitter_throws': hitter_throws,
        'lineup_status': lineup_status,
        'batting_order_status': batting_order_status,
        'batting_order_spot': batting_order_spot,
        'batting_order_raw': lineup_player.get('batting_order_raw'),
        'lineup_source': 'MLB StatsAPI boxscore battingOrder' if lineup_player else None,
        'ros_dollars': round(_safe_float(value.get('dollars')) or 0.0, 1),
        'ros_rpts': round(_safe_float(value.get('rpts')) or 0.0, 1),
        'team_has_game_today': bool(today_games) if team else None,
        'team_game_count_next_7': len({g.get('date') for g in games if g.get('date')}),
        'team_left_pct': team_hand.get('left_pct'),
        'team_right_pct': team_hand.get('right_pct'),
        'opponent_today': today_game.get('opponent'),
        'home_away_today': today_game.get('home_away'),
        'game_pk_today': today_game.get('game_pk'),
        'game_datetime_today': today_game.get('game_datetime'),
        'venue_name_today': today_game.get('venue_name'),
        'park_today': today_game.get('park'),
        'park_factor_today': today_game.get('park_factor'),
        'roof_type_today': today_game.get('roof_type'),
        'is_indoor_or_dome_today': today_game.get('is_indoor_or_dome'),
        'weather_source_today': today_game.get('weather_source'),
        'weather_temp_f_today': today_game.get('weather_temp_f'),
        'weather_wind_speed_mph_today': today_game.get('weather_wind_speed_mph'),
        'weather_note_today': today_game.get('weather_note'),
        'opposing_probable_pitcher': today_game.get('opposing_probable_pitcher'),
        'opposing_probable_pitcher_id': today_game.get('opposing_probable_pitcher_id'),
        'opposing_pitcher_team': today_game.get('probable_pitcher_team'),
        'opposing_probable_source': today_game.get('probable_source'),
        'opposing_pitcher_hand': opp_hand,
        'hitter_platoon_context': platoon_context.get('label'),
        'hitter_platoon_note': platoon_context.get('note'),
        'hitter_platoon_detail': platoon_context.get('detail'),
        'opposing_pitcher_projected_pts': today_game.get('opposing_pitcher_projected_pts'),
        'opposing_pitcher_tier': today_game.get('opposing_pitcher_tier'),
        'opposing_pitcher_proj_era': today_game.get('opposing_pitcher_proj_era'),
        'opposing_pitcher_proj_whip': today_game.get('opposing_pitcher_proj_whip'),
        'opposing_pitcher_proj_k9': today_game.get('opposing_pitcher_proj_k9'),
        'opposing_pitcher_xera': today_game.get('opposing_pitcher_xera'),
        'opposing_pitcher_fip': today_game.get('opposing_pitcher_fip'),
        'opposing_pitcher_xfip': today_game.get('opposing_pitcher_xfip'),
        'opposing_pitcher_siera': today_game.get('opposing_pitcher_siera'),
        'opposing_pitcher_hard_hit_pct': today_game.get('opposing_pitcher_hard_hit_pct'),
        'opposing_pitcher_barrel_pct': today_game.get('opposing_pitcher_barrel_pct'),
        'opposing_pitcher_whiff_pct': today_game.get('opposing_pitcher_whiff_pct'),
        'opposing_pitcher_k_pct': today_game.get('opposing_pitcher_k_pct'),
        'opposing_pitcher_bb_pct': today_game.get('opposing_pitcher_bb_pct'),
        'context_note': '; '.join(dict.fromkeys(notes)),
    }


def build_hitter_daily_context(base_date=None, players_list=None, matchup_snapshot_data=None,
                               prediction_records=None, allow_live_snapshot=True,
                               team_handedness_context=None):
    """Build logged-only hitter daily context for future modeling; no scoring changes."""
    base_date = base_date or date.today().isoformat()
    players_list = [dict(p) for p in (players_list or [])]
    if prediction_records is None:
        prediction_records, _source_kind, _source_label = _matchup_prediction_records_for_actions(
            base_date,
            days=6,
            records=None,
            source=None,
        )
    snapshot = matchup_snapshot_data
    if snapshot is None and allow_live_snapshot:
        try:
            snapshot = build_matchup_snapshot()
        except Exception as e:
            snapshot = {'error': f'{type(e).__name__}: {e}'}
    lookup = _hitter_lookup(players_list)
    game_context = _hitter_game_context_by_team(prediction_records or [], base_date, days=6)
    team_handedness = team_handedness_context
    if team_handedness is None:
        team_handedness, _team_hand_age = _load_streaming_cache('team_handedness.json', max_age_hours=168)
    team_handedness = team_handedness if isinstance(team_handedness, dict) else {}
    lineup_context = _fetch_hitter_lineup_context(prediction_records or [], base_date)
    rows = []
    if snapshot and not snapshot.get('error') and not snapshot.get('low_confidence'):
        active = [row for row in snapshot.get('my_active') or [] if _matchup_player_is_hitter(row)]
        bench = [row for row in snapshot.get('my_bench') or [] if _matchup_player_is_hitter(row)]
        for row in active:
            rows.append(_hitter_context_row(row, lookup, game_context, base_date, 'active', team_handedness, lineup_context))
        for row in bench:
            rows.append(_hitter_context_row(row, lookup, game_context, base_date, 'bench', team_handedness, lineup_context))
    fa_rows = [
        row for row in _hitter_player_rows(players_list)
        if row.get('status') in ('FA', 'WAIVER') and (_safe_float(row.get('dollars')) or 0.0) > 0
    ]
    fa_rows.sort(key=lambda p: (_safe_float(p.get('dollars')) or 0.0, _safe_float(p.get('rpts')) or 0.0), reverse=True)
    for row in fa_rows[:20]:
        pseudo = {
            'name': row.get('name'),
            'team': row.get('team'),
            'espn_id': row.get('espn_id'),
            'fg_id': row.get('fg_id'),
            'slot': row.get('displayPos') or row.get('best_pos'),
            'status': row.get('status'),
        }
        rows.append(_hitter_context_row(pseudo, lookup, game_context, base_date, 'available', team_handedness, lineup_context))
    total = len(rows)
    with_game = sum(1 for row in rows if row.get('team_has_game_today') is True)
    with_opp = sum(1 for row in rows if row.get('opponent_today'))
    injured = sum(1 for row in rows if row.get('injury_status'))
    with_pitcher_quality = sum(1 for row in rows if row.get('opposing_pitcher_projected_pts') is not None)
    with_park = sum(1 for row in rows if row.get('park_factor_today') is not None or row.get('venue_name_today'))
    with_team_hand = sum(1 for row in rows if row.get('team_left_pct') is not None)
    return {
        'date': base_date,
        'rows': rows,
        'coverage': {
            'total_rows': total,
            'with_game_today': with_game,
            'with_opponent_today': with_opp,
            'with_ros_value': sum(1 for row in rows if row.get('ros_rpts') is not None),
            'with_opposing_pitcher': sum(1 for row in rows if row.get('opposing_probable_pitcher')),
            'with_opposing_pitcher_id': sum(1 for row in rows if row.get('opposing_probable_pitcher_id')),
            'with_opposing_pitcher_hand': sum(1 for row in rows if row.get('opposing_pitcher_hand')),
            'with_opposing_pitcher_quality': with_pitcher_quality,
            'with_park_or_venue': with_park,
            'with_team_handedness_context': with_team_hand,
            'with_hitter_bats': sum(1 for row in rows if row.get('hitter_bats')),
            'with_hitter_throws': sum(1 for row in rows if row.get('hitter_throws')),
            'with_hitter_platoon_context': sum(1 for row in rows if row.get('hitter_platoon_context') and row.get('hitter_platoon_context') != 'unknown'),
            'hitter_platoon_edge': sum(1 for row in rows if row.get('hitter_platoon_context') == 'platoon_edge'),
            'hitter_platoon_risk': sum(1 for row in rows if row.get('hitter_platoon_context') == 'platoon_risk'),
            'hitter_switch_context': sum(1 for row in rows if row.get('hitter_platoon_context') == 'switch_hitter'),
            'with_confirmed_lineup_status': sum(1 for row in rows if row.get('lineup_status') != 'unknown'),
            'with_lineup_spot': sum(1 for row in rows if row.get('batting_order_spot') is not None),
            'injury_status_rows': injured,
            'team_game_context_teams': len(game_context),
            'teams_with_posted_lineups': len((lineup_context or {}).get('teams_with_posted_lineups') or []),
        },
        'notes': [
            'Logged-only context for future hitter modeling; not used in scoring or recommendations.',
            'Opposing pitcher quality, park, venue, roof, and weather context come from existing prediction records when available.',
            'Hitter handedness comes from MLB active-roster metadata when available; lineup status comes from posted MLB boxscore batting orders.',
            'Opposing pitcher handedness remains null when current probable data does not expose pitchHand.',
        ],
    }


def _hitter_action(kind, text, priority, row=None, value=None, source='espn_roster'):
    row = row or {}
    value = value or {}
    confidence = _hitter_context_confidence(row)
    meta = {'source': source}
    if confidence:
        meta['context'] = confidence
    return {
        'kind': kind,
        'text': _compact_decision_text(text, 180),
        'priority': priority,
        'name': row.get('name') or '',
        'team': row.get('team') or '',
        'slot': row.get('slot') or '',
        'status': row.get('status') or value.get('status') or '',
        'dollars': round(_safe_float(value.get('dollars')) or 0.0, 1),
        'rpts': round(_safe_float(value.get('rpts')) or 0.0, 1),
        'source': source,
        'context_confidence': confidence,
        'meta': meta,
    }


def _hitter_context_confidence(row):
    if not row or 'team_has_game_today' not in row:
        return None
    has_game = row.get('team_has_game_today') is True
    has_bats = bool(row.get('hitter_bats'))
    has_opp_hand = bool(row.get('opposing_pitcher_hand'))
    has_lineup_spot = row.get('batting_order_spot') is not None
    has_platoon = row.get('hitter_platoon_context') not in (None, '', 'unknown')
    if has_game and has_bats and has_opp_hand and has_lineup_spot:
        return 'High context'
    if has_game and has_platoon:
        return 'Medium context'
    return 'Low context'


def _hitter_context_action_value(row):
    return {
        'dollars': _safe_float((row or {}).get('ros_dollars')) or 0.0,
        'rpts': _safe_float((row or {}).get('ros_rpts')) or 0.0,
        'status': (row or {}).get('roster_status') or '',
    }


def _hitter_context_candidate_key(row):
    lineup_status = (row or {}).get('lineup_status') or ''
    lineup_score = 3 if lineup_status == 'confirmed_starting' else 1 if lineup_status == 'unknown' else 0
    platoon = (row or {}).get('hitter_platoon_context') or ''
    platoon_score = 2 if platoon == 'platoon_edge' else 1 if platoon == 'switch_hitter' else -1 if platoon == 'platoon_risk' else 0
    spot = (row or {}).get('batting_order_spot')
    spot_score = 0 if spot is None else max(0, 10 - int(spot))
    return (
        _safe_float((row or {}).get('ros_dollars')) or 0.0,
        lineup_score,
        platoon_score,
        spot_score,
        _safe_float((row or {}).get('ros_rpts')) or 0.0,
    )


def _hitter_context_matchup_text(row):
    if not row:
        return ''
    bits = []
    if row.get('home_away_today') and row.get('opponent_today'):
        bits.append(f"{row.get('home_away_today')} vs {row.get('opponent_today')}")
    if row.get('batting_order_spot') is not None:
        bits.append(f"batting {row.get('batting_order_spot')}")
    elif row.get('lineup_status') and row.get('lineup_status') != 'unknown':
        bits.append(str(row.get('lineup_status')).replace('_', ' '))
    if row.get('hitter_platoon_note') and row.get('hitter_platoon_context') != 'unknown':
        bits.append(row.get('hitter_platoon_note'))
    if row.get('opposing_probable_pitcher'):
        hand = row.get('opposing_pitcher_hand') or '?'
        bits.append(f"vs {row.get('opposing_probable_pitcher')} ({hand})")
    return '; '.join(bits)


def _hitter_context_replacement_text(candidate, source_label):
    if not candidate:
        return ''
    bits = []
    if candidate.get('home_away_today') and candidate.get('opponent_today'):
        bits.append(f"{candidate.get('home_away_today')} vs {candidate.get('opponent_today')}")
    if candidate.get('batting_order_spot') is not None:
        bits.append(f"batting {candidate.get('batting_order_spot')}")
    if candidate.get('hitter_platoon_note') and candidate.get('hitter_platoon_context') != 'unknown':
        bits.append(candidate.get('hitter_platoon_note'))
    detail = f"{candidate.get('name')} (${(_safe_float(candidate.get('ros_dollars')) or 0.0):.1f})"
    if bits:
        detail += f", {'; '.join(bits)}"
    return f" {source_label}: {detail}. Check eligibility."


def _best_hitter_context_replacement(rows):
    candidates = [
        row for row in rows or []
        if row.get('team_has_game_today') is True
        and not row.get('injury_status')
        and row.get('lineup_status') != 'not_in_confirmed_lineup'
    ]
    if not candidates:
        return None
    return max(candidates, key=_hitter_context_candidate_key)


def build_hitter_decision_summary(base_date=None, players_list=None, matchup_snapshot_data=None,
                                  prediction_records=None, limit=10, allow_live_snapshot=True,
                                  team_handedness_context=None):
    """Read-only hitter lineup/FA suggestions from ESPN roster rows + RoS values."""
    base_date = base_date or date.today().isoformat()
    players_list = [dict(p) for p in (players_list or [])]
    roster_status_cache, roster_status_sources = _load_local_roster_status_cache()
    for player in players_list:
        if player.get('status'):
            continue
        status = roster_status_cache.get((normalize_name(player.get('name') or ''), player.get('team') or ''))
        if status:
            player['status'] = status
    notes = []
    data_available = {
        'ros_values': bool(players_list),
        'espn_roster': False,
        'team_game_schedule': False,
        'roster_status_cache': bool(roster_status_cache),
    }
    if prediction_records is None:
        prediction_records, _source_kind, _source_label = _matchup_prediction_records_for_actions(
            base_date,
            days=0,
            records=None,
            source=None,
        )
    today_teams = _matchup_today_team_set(prediction_records or [], base_date)
    data_available['team_game_schedule'] = bool(today_teams)
    if not today_teams:
        notes.append('Team game schedule was not available from current prediction records; no-game checks were skipped.')
    if roster_status_sources:
        notes.append(f"Roster status cache used for FA/roster labels: {os.path.basename(roster_status_sources[0])}.")

    snapshot = matchup_snapshot_data
    if snapshot is None and allow_live_snapshot:
        try:
            snapshot = build_matchup_snapshot()
        except Exception as e:
            snapshot = {'error': f'{type(e).__name__}: {e}'}
    if snapshot and not snapshot.get('error') and not snapshot.get('low_confidence'):
        data_available['espn_roster'] = True
    elif snapshot and snapshot.get('error'):
        notes.append(f"ESPN roster data unavailable: {snapshot.get('error')}")
    else:
        notes.append('ESPN roster data unavailable; showing FA/waiver hitter value only.')

    lookup = _hitter_lookup(players_list)
    actions = []
    seen = set()

    def add(action):
        key = (action.get('kind'), normalize_name(action.get('name') or ''), action.get('text'))
        if key in seen:
            return
        seen.add(key)
        actions.append(action)

    active = [row for row in (snapshot or {}).get('my_active') or [] if _matchup_player_is_hitter(row)]
    bench = [row for row in (snapshot or {}).get('my_bench') or [] if _matchup_player_is_hitter(row)]
    if team_handedness_context is None:
        try:
            team_handedness_context = fetch_team_handedness()
        except Exception:
            team_handedness_context, _age = _load_streaming_cache('team_handedness.json', max_age_hours=168)
    daily_context = build_hitter_daily_context(
        base_date,
        players_list=players_list,
        matchup_snapshot_data=snapshot,
        prediction_records=prediction_records,
        allow_live_snapshot=False,
        team_handedness_context=team_handedness_context,
    )
    context_rows = daily_context.get('rows') or []
    active_context = [row for row in context_rows if row.get('roster_state') == 'active']
    active_context_by_name = {normalize_name(row.get('name') or ''): row for row in active_context}
    bench_context = [row for row in context_rows if row.get('roster_state') == 'bench']
    available_context = [row for row in context_rows if row.get('roster_state') == 'available']
    best_bench_context = _best_hitter_context_replacement(bench_context)
    best_fa_context = _best_hitter_context_replacement(available_context)
    active_hurt = [row for row in active if row.get('injury')]
    bench_usable = [
        row for row in bench
        if not row.get('injury') and _hitter_team_has_game(row, today_teams) is not False
    ]
    bench_usable.sort(key=lambda r: _hitter_value(r, lookup)['dollars'], reverse=True)

    for row in active_hurt:
        context_row = dict(active_context_by_name.get(normalize_name(row.get('name') or '')) or {})
        action_row = {**context_row, **{k: v for k, v in row.items() if v not in (None, '')}}
        value = _hitter_value(row, lookup)
        repl_text = (
            _hitter_context_replacement_text(best_bench_context, 'Best bench')
            or _hitter_context_replacement_text(best_fa_context, 'Best FA')
        )
        add(_hitter_action(
            'INJURY CHECK',
            f"Check {row.get('name')} in active {row.get('slot')}: ESPN status {row.get('injury')}.{repl_text}",
            5,
            action_row,
            value,
        ))

    if today_teams:
        active_no_game = [row for row in active_context if not row.get('injury_status') and row.get('team_has_game_today') is False]
        for row in sorted(active_no_game, key=_hitter_context_candidate_key)[:3]:
            value = _hitter_context_action_value(row)
            repl_text = (
                _hitter_context_replacement_text(best_bench_context, 'Best bench')
                or _hitter_context_replacement_text(best_fa_context, 'Best FA')
            )
            add(_hitter_action(
                'NO GAME',
                f"{row.get('name')} appears active at {row.get('slot')} with no game today.{repl_text}",
                20,
                row,
                value,
            ))

    active_missing_lineup = [
        row for row in active_context
        if not row.get('injury_status')
        and row.get('team_has_game_today') is not False
        and row.get('lineup_status') == 'not_in_confirmed_lineup'
    ]
    for row in sorted(active_missing_lineup, key=_hitter_context_candidate_key)[:3]:
        value = _hitter_context_action_value(row)
        repl_text = (
            _hitter_context_replacement_text(best_bench_context, 'Best bench')
            or _hitter_context_replacement_text(best_fa_context, 'Best FA')
        )
        add(_hitter_action(
            'BENCH',
            f"{row.get('name')} is active but not in the posted lineup yet.{repl_text}",
            24,
            row,
            value,
        ))

    bench_context_usable = [
        row for row in bench_context
        if row.get('team_has_game_today') is True
        and not row.get('injury_status')
        and row.get('lineup_status') != 'not_in_confirmed_lineup'
    ]
    bench_context_usable.sort(key=_hitter_context_candidate_key, reverse=True)
    for row in bench_context_usable[:3]:
        value = _hitter_context_action_value(row)
        if value['dollars'] <= 0 and not active_hurt and not active_missing_lineup:
            continue
        label = 'START' if active_hurt or value['dollars'] >= 5 else 'WATCH'
        matchup = _hitter_context_matchup_text(row)
        matchup_text = f" {matchup}." if matchup else ""
        add(_hitter_action(
            label,
            f"{row.get('name')} is on bench with a game today; ${value['dollars']:.1f} RoS value.{matchup_text}",
            28 if label == 'START' else 55,
            row,
            value,
        ))

    fa_hitters = [
        row for row in _hitter_player_rows(players_list)
        if row.get('status') in ('FA', 'WAIVER') and (_safe_float(row.get('dollars')) or 0.0) > 0
    ]
    fa_hitters.sort(key=lambda p: (_safe_float(p.get('dollars')) or 0.0, _safe_float(p.get('rpts')) or 0.0), reverse=True)
    fa_context_candidates = [
        row for row in available_context
        if row.get('team_has_game_today') is True
        and row.get('lineup_status') != 'not_in_confirmed_lineup'
        and (_safe_float(row.get('ros_dollars')) or 0.0) > 0
    ]
    fa_context_candidates.sort(key=_hitter_context_candidate_key, reverse=True)
    if fa_context_candidates:
        for row in fa_context_candidates[:4]:
            value = _hitter_context_action_value(row)
            matchup = _hitter_context_matchup_text(row)
            matchup_text = f" {matchup}." if matchup else ""
            add(_hitter_action(
                'ADD',
                f"Watch/add {row.get('name')} if you need hitter depth; ${value['dollars']:.1f} RoS value.{matchup_text}",
                65,
                row,
                value,
                source='hitter_context',
            ))
    else:
        for player in fa_hitters[:4]:
            add(_hitter_action(
                'ADD',
                f"Watch/add {player.get('name')} if you need hitter depth; ${_safe_float(player.get('dollars')) or 0.0:.1f} RoS value.",
                65,
                {'name': player.get('name'), 'team': player.get('team'), 'slot': player.get('displayPos') or player.get('best_pos')},
                player,
                source='ros_values',
            ))

    actions = sorted(actions, key=lambda a: (a.get('priority', 99), -(_safe_float(a.get('dollars')) or 0.0), a.get('text')))[:limit]
    return {
        'date': base_date,
        'items': actions,
        'count': len(actions),
        'notes': notes,
        'data_available': data_available,
        'today_team_count': len(today_teams),
        'active_hitter_count': len(active),
        'bench_hitter_count': len(bench),
        'fa_hitter_candidates': len(fa_hitters),
        'daily_context': daily_context,
    }


def print_hitter_decisions(summary):
    print("\nHITTER DECISIONS")
    print("=" * 60)
    print("Read-only: uses ESPN roster rows, current RoS hitter values, and team game availability when detectable.")
    data = (summary or {}).get('data_available') or {}
    context = (summary or {}).get('daily_context') or {}
    coverage = context.get('coverage') or {}
    print(
        "Data: "
        f"RoS values={'yes' if data.get('ros_values') else 'no'}, "
        f"ESPN roster={'yes' if data.get('espn_roster') else 'no'}, "
        f"team games={'yes' if data.get('team_game_schedule') else 'no'}"
    )
    if coverage:
        print(
            "Logged hitter context: "
            f"{coverage.get('total_rows', 0)} rows, "
            f"{coverage.get('with_game_today', 0)} with game today, "
            f"{coverage.get('with_opponent_today', 0)} with opponent, "
            f"{coverage.get('with_opposing_pitcher_quality', 0)} with pitcher quality, "
            f"{coverage.get('with_park_or_venue', 0)} with park/venue, "
            f"{coverage.get('with_hitter_bats', 0)} with hitter bats, "
            f"{coverage.get('with_hitter_platoon_context', 0)} with platoon context, "
            f"{coverage.get('with_lineup_spot', 0)} with lineup spot"
        )
    items = (summary or {}).get('items') or []
    if not items:
        print("  None")
    for idx, action in enumerate(items[:10], 1):
        meta = []
        if action.get('team'):
            meta.append(action.get('team'))
        if action.get('slot'):
            meta.append(action.get('slot'))
        if action.get('context_confidence'):
            meta.append(action.get('context_confidence'))
        meta.append(f"${(_safe_float(action.get('dollars')) or 0.0):.1f} RoS")
        suffix = f" [{' | '.join(meta)}]" if meta else ""
        print(f"{idx:>2}. {action.get('kind')}: {action.get('text')}{suffix}")
    notes = (summary or {}).get('notes') or []
    if notes:
        print("\nNotes")
        for note in notes:
            print(f"  - {note}")


def _hitter_decision_log_path(target_date):
    os.makedirs(HITTER_DECISIONS_DIR, exist_ok=True)
    return os.path.join(HITTER_DECISIONS_DIR, f"{target_date}.jsonl")


def write_hitter_decision_log(summary, source='report'):
    """Write generated hitter decision actions for later evaluation."""
    if not summary:
        return None
    target_date = summary.get('date') or date.today().isoformat()
    items = summary.get('items') or []
    context = summary.get('daily_context') or {}
    coverage = context.get('coverage') or {}
    logged_at = datetime.now().isoformat(timespec='seconds')
    rows = []
    for idx, item in enumerate(items, 1):
        rows.append({
            'date': target_date,
            'logged_at': logged_at,
            'source': source,
            'rank': idx,
            'kind': item.get('kind'),
            'name': item.get('name'),
            'team': item.get('team'),
            'slot': item.get('slot'),
            'status': item.get('status'),
            'dollars': item.get('dollars'),
            'rpts': item.get('rpts'),
            'context_confidence': item.get('context_confidence'),
            'text': item.get('text'),
            'action_source': item.get('source'),
            'coverage': {
                'total_rows': coverage.get('total_rows'),
                'with_game_today': coverage.get('with_game_today'),
                'with_hitter_bats': coverage.get('with_hitter_bats'),
                'with_hitter_platoon_context': coverage.get('with_hitter_platoon_context'),
                'with_lineup_spot': coverage.get('with_lineup_spot'),
                'teams_with_posted_lineups': coverage.get('teams_with_posted_lineups'),
            },
        })
    path = _hitter_decision_log_path(target_date)
    with open(path, 'w') as f:
        for row in rows:
            f.write(json.dumps(row, sort_keys=True) + '\n')
    return path


def _read_hitter_decision_log_rows():
    rows = []
    if not os.path.isdir(HITTER_DECISIONS_DIR):
        return rows
    for fn in sorted(os.listdir(HITTER_DECISIONS_DIR)):
        if not fn.endswith('.jsonl'):
            continue
        path = os.path.join(HITTER_DECISIONS_DIR, fn)
        try:
            with open(path, 'r') as f:
                for line in f:
                    line = line.strip()
                    if not line:
                        continue
                    try:
                        rows.append(json.loads(line))
                    except Exception:
                        continue
        except Exception:
            continue
    return rows


def audit_hitter_decision_log():
    rows = _read_hitter_decision_log_rows()
    print("\nHITTER DECISION LOG AUDIT")
    print("=" * 60)
    print("Read-only: summarizes generated hitter decision logs; no recommendations are changed.")
    if not rows:
        print("No hitter decision logs found yet.")
        print(f"Log folder: {HITTER_DECISIONS_DIR}")
        print("Run a normal report or preview to create today's generated hitter decision log.")
        return {'rows': 0}
    dates = sorted({row.get('date') for row in rows if row.get('date')})
    kind_counts = Counter(row.get('kind') or 'UNKNOWN' for row in rows)
    confidence_counts = Counter(row.get('context_confidence') or 'No label' for row in rows)
    print(f"Log folder: {HITTER_DECISIONS_DIR}")
    print(f"Dates logged: {dates[0]} through {dates[-1]} ({len(dates)} date(s))")
    print(f"Action rows: {len(rows)}")
    print("Action types: " + ", ".join(f"{kind} {count}" for kind, count in sorted(kind_counts.items())))
    print("Context confidence: " + ", ".join(f"{label} {confidence_counts[label]}" for label in sorted(confidence_counts)))
    latest = [row for row in rows if row.get('date') == dates[-1]]
    print(f"\nLatest date: {dates[-1]}")
    for row in latest[:8]:
        print(
            f"  - {row.get('kind')}: {row.get('name')} "
            f"({row.get('team') or '?'}, {row.get('context_confidence') or 'No label'})"
        )
    print("\nThis is an evaluation foundation only. It does not use hitter outcomes yet.")
    return {'rows': len(rows), 'dates': len(dates)}


def print_hitter_context(context, limit=12):
    print("\nHITTER DAILY CONTEXT")
    print("=" * 60)
    print("Logged-only: collected for future hitter modeling; not used in scoring or recommendations.")
    coverage = (context or {}).get('coverage') or {}
    print(
        f"Rows: {coverage.get('total_rows', 0)} | "
        f"game today: {coverage.get('with_game_today', 0)} | "
        f"opponent: {coverage.get('with_opponent_today', 0)} | "
        f"pitcher quality: {coverage.get('with_opposing_pitcher_quality', 0)} | "
        f"park/venue: {coverage.get('with_park_or_venue', 0)} | "
        f"pitcher hand: {coverage.get('with_opposing_pitcher_hand', 0)} | "
        f"hitter bats: {coverage.get('with_hitter_bats', 0)} | "
        f"platoon context: {coverage.get('with_hitter_platoon_context', 0)} | "
        f"lineup spot: {coverage.get('with_lineup_spot', 0)} | "
        f"posted lineup teams: {coverage.get('teams_with_posted_lineups', 0)}"
    )
    rows = (context or {}).get('rows') or []
    for row in rows[:limit]:
        game = 'game' if row.get('team_has_game_today') else 'no game'
        opp = row.get('opponent_today') or '?'
        pitcher = row.get('opposing_probable_pitcher') or 'probable TBD'
        pitcher_pts = row.get('opposing_pitcher_projected_pts')
        pitcher_quality = f"{pitcher}, {pitcher_pts:.1f} pitcher pts" if pitcher_pts is not None else pitcher
        hand = row.get('opposing_pitcher_hand') or 'pitcher hand TODO'
        bats = row.get('hitter_bats') or 'bats TODO'
        platoon = row.get('hitter_platoon_note') or 'platoon TODO'
        lineup = (
            f"batting {row.get('batting_order_spot')}"
            if row.get('batting_order_spot') is not None
            else row.get('lineup_status') or 'lineup unknown'
        )
        print(
            f"  - {row.get('name')} ({row.get('roster_state')}, {row.get('team')}, "
            f"{row.get('slot') or row.get('display_pos')}): {game} vs {opp}; "
            f"${row.get('ros_dollars')} RoS; opp SP {pitcher_quality}; "
            f"{row.get('park_today') or row.get('venue_name_today') or 'park TODO'}; "
            f"bats {bats}; {hand}; {platoon}; {lineup}"
        )
    notes = (context or {}).get('notes') or []
    if notes:
        print("\nNotes")
        for note in notes:
            print(f"  - {note}")


def _hitter_context_score(row):
    return (
        _safe_float((row or {}).get('ros_dollars')) or 0.0,
        _safe_float((row or {}).get('ros_rpts')) or 0.0,
    )


def _hitter_context_name(row):
    name = (row or {}).get('name') or 'Unknown'
    team = (row or {}).get('team') or '?'
    slot = (row or {}).get('slot') or (row or {}).get('display_pos') or '?'
    value = _safe_float((row or {}).get('ros_dollars')) or 0.0
    return f"{name} ({team}, {slot}, ${value:.1f} RoS)"


def _print_hitter_context_rows(title, rows, limit=6, empty='None'):
    print(f"\n{title}")
    if not rows:
        print(f"  {empty}")
        return
    for row in rows[:limit]:
        details = []
        if row.get('injury_status'):
            details.append(f"injury {row.get('injury_status')}")
        if row.get('team_has_game_today') is False:
            details.append('no game today')
        elif row.get('opponent_today'):
            details.append(f"{row.get('home_away_today') or '?'} vs {row.get('opponent_today')}")
        if row.get('lineup_status') and row.get('lineup_status') != 'unknown':
            lineup = row.get('lineup_status')
            if row.get('batting_order_spot') is not None:
                lineup += f", batting {row.get('batting_order_spot')}"
            details.append(lineup)
        if row.get('opposing_probable_pitcher'):
            hand = row.get('opposing_pitcher_hand') or '?'
            pts = row.get('opposing_pitcher_projected_pts')
            pitcher = f"opp SP {row.get('opposing_probable_pitcher')} ({hand})"
            if pts is not None:
                pitcher += f", {pts:.1f} pitcher pts"
            details.append(pitcher)
        if row.get('hitter_bats'):
            details.append(f"bats {row.get('hitter_bats')}")
        if row.get('hitter_platoon_note') and row.get('hitter_platoon_context') != 'unknown':
            details.append(row.get('hitter_platoon_note'))
        suffix = f" — {'; '.join(details)}" if details else ''
        print(f"  - {_hitter_context_name(row)}{suffix}")


def build_hitter_decision_context_analysis(base_date=None, players_list=None):
    """Read-only hitter decision context analysis; no recommendation changes."""
    base_date = base_date or date.today().isoformat()
    players_list = [dict(p) for p in (players_list or [])]
    records, source_kind, source_label = _matchup_prediction_records_for_actions(base_date, days=6)
    snapshot = None
    try:
        snapshot = build_matchup_snapshot()
    except Exception as e:
        snapshot = {'error': f'{type(e).__name__}: {e}'}
    try:
        team_handedness = fetch_team_handedness()
    except Exception:
        team_handedness, _age = _load_streaming_cache('team_handedness.json', max_age_hours=168)
    team_handedness = team_handedness if isinstance(team_handedness, dict) else {}
    context = build_hitter_daily_context(
        base_date,
        players_list=players_list,
        matchup_snapshot_data=snapshot,
        prediction_records=records,
        allow_live_snapshot=False,
        team_handedness_context=team_handedness,
    )
    rows = context.get('rows') or []
    active = [r for r in rows if r.get('roster_state') == 'active']
    bench = [r for r in rows if r.get('roster_state') == 'bench']
    available = [r for r in rows if r.get('roster_state') == 'available']

    active_injured = sorted(
        [r for r in active if r.get('injury_status')],
        key=_hitter_context_score,
        reverse=True,
    )
    active_no_game = sorted(
        [r for r in active if r.get('team_has_game_today') is False and not r.get('injury_status')],
        key=_hitter_context_score,
    )
    active_missing_lineup = sorted(
        [r for r in active if r.get('lineup_status') == 'not_in_confirmed_lineup'],
        key=_hitter_context_score,
        reverse=True,
    )
    risky_active = active_injured + active_no_game + active_missing_lineup
    risky_floor = min([_hitter_context_score(r)[0] for r in risky_active], default=None)
    bench_with_game = [
        r for r in bench
        if r.get('team_has_game_today') is True and not r.get('injury_status')
    ]
    if risky_floor is not None:
        bench_better = [r for r in bench_with_game if (_hitter_context_score(r)[0] > risky_floor)]
    else:
        bench_better = bench_with_game
    bench_better = sorted(bench_better, key=_hitter_context_score, reverse=True)
    fa_replacements = sorted(
        [
            r for r in available
            if r.get('team_has_game_today') is not False
            and not r.get('injury_status')
            and (_safe_float(r.get('ros_dollars')) or 0.0) > 0
        ],
        key=_hitter_context_score,
        reverse=True,
    )
    return {
        'date': base_date,
        'prediction_source': source_label or source_kind,
        'snapshot_available': bool(snapshot and not snapshot.get('error') and not snapshot.get('low_confidence')),
        'snapshot_error': (snapshot or {}).get('error') or ('low confidence matchup snapshot' if (snapshot or {}).get('low_confidence') else None),
        'context': context,
        'active_injured': active_injured,
        'active_no_game': active_no_game,
        'active_missing_lineup': active_missing_lineup,
        'bench_better': bench_better,
        'fa_replacements': fa_replacements,
        'notes': context.get('notes') or [],
    }


def print_hitter_decision_context_analysis(summary):
    print("\nHITTER DECISION CONTEXT ANALYSIS")
    print("=" * 60)
    print("Analysis only: this does not change scoring, predictions, recommendations, or roster moves.")
    print(f"Date: {summary.get('date')}")
    print(f"Prediction context source: {summary.get('prediction_source') or 'unknown'}")
    if summary.get('snapshot_error'):
        print(f"ESPN matchup/roster snapshot note: {summary.get('snapshot_error')}")
    context = summary.get('context') or {}
    coverage = context.get('coverage') or {}
    total = coverage.get('total_rows', 0)
    print("\nContext coverage")
    print(f"  Rows analyzed: {total}")
    print(f"  Team game known/today: {coverage.get('with_game_today', 0)}/{total}")
    print(f"  Hitter bats known: {coverage.get('with_hitter_bats', 0)}/{total}")
    print(f"  Opposing pitcher hand known: {coverage.get('with_opposing_pitcher_hand', 0)}/{total}")
    print(f"  Platoon context known: {coverage.get('with_hitter_platoon_context', 0)}/{total}")
    print(
        f"    edge {coverage.get('hitter_platoon_edge', 0)}, "
        f"risk {coverage.get('hitter_platoon_risk', 0)}, "
        f"switch {coverage.get('hitter_switch_context', 0)}"
    )
    print(f"  Lineup status known: {coverage.get('with_confirmed_lineup_status', 0)}/{total}")
    print(f"  Batting order spot known: {coverage.get('with_lineup_spot', 0)}/{total}")
    print(f"  Injury status rows: {coverage.get('injury_status_rows', 0)}")
    print(f"  Posted lineup teams: {coverage.get('teams_with_posted_lineups', 0)}")

    _print_hitter_context_rows(
        "Active hitters with injury/DTD/IL/OUT status",
        summary.get('active_injured') or [],
        empty='No active hitter injury flags found.',
    )
    _print_hitter_context_rows(
        "Active hitters with no game today",
        summary.get('active_no_game') or [],
        empty='No active hitter no-game spots found.',
    )
    _print_hitter_context_rows(
        "Active hitters missing confirmed lineup spot",
        summary.get('active_missing_lineup') or [],
        empty='No active hitters missing from posted lineups, or lineups not posted yet.',
    )
    _print_hitter_context_rows(
        "Bench hitters with game today and better RoS value than risky active spots",
        summary.get('bench_better') or [],
        empty='No clear bench replacements found from current context.',
    )
    _print_hitter_context_rows(
        "Best FA/waiver hitter replacements by RoS value",
        summary.get('fa_replacements') or [],
        empty='No positive RoS FA/waiver hitter replacements found.',
    )

    notes = summary.get('notes') or []
    if notes:
        print("\nNotes / TODO")
        for note in notes:
            print(f"  - {note}")
    print("\nCurrent hitter recommendations are unchanged. Use this to see where context is reliable enough for future modeling.")


def _pct(count, total):
    if not total:
        return "0%"
    return f"{round(count / total * 100)}%"


def print_hitter_context_coverage_audit(summary, decision_summary=None):
    print("\nHITTER CONTEXT COVERAGE AUDIT")
    print("=" * 60)
    print("Read-only: measures hitter context reliability; recommendations are unchanged.")
    print(f"Date: {summary.get('date')}")
    print(f"Prediction context source: {summary.get('prediction_source') or 'unknown'}")
    if summary.get('snapshot_error'):
        print(f"ESPN matchup/roster snapshot note: {summary.get('snapshot_error')}")
    context = summary.get('context') or {}
    coverage = context.get('coverage') or {}
    rows = context.get('rows') or []
    total = coverage.get('total_rows', len(rows))

    checks = [
        ('Team game today', coverage.get('with_game_today', 0)),
        ('Opponent known', coverage.get('with_opponent_today', 0)),
        ('Opposing pitcher known', coverage.get('with_opposing_pitcher', 0)),
        ('Opposing pitcher hand', coverage.get('with_opposing_pitcher_hand', 0)),
        ('Opposing pitcher quality', coverage.get('with_opposing_pitcher_quality', 0)),
        ('Hitter bats', coverage.get('with_hitter_bats', 0)),
        ('Platoon context', coverage.get('with_hitter_platoon_context', 0)),
        ('Lineup status', coverage.get('with_confirmed_lineup_status', 0)),
        ('Lineup spot', coverage.get('with_lineup_spot', 0)),
        ('Park/venue', coverage.get('with_park_or_venue', 0)),
    ]
    print("\nCoverage")
    print(f"  Rows analyzed: {total}")
    for label, count in checks:
        print(f"  {label}: {count}/{total} ({_pct(count, total)})")
    print(
        "  Platoon split: "
        f"edge {coverage.get('hitter_platoon_edge', 0)}, "
        f"risk {coverage.get('hitter_platoon_risk', 0)}, "
        f"switch {coverage.get('hitter_switch_context', 0)}"
    )
    print(f"  Posted lineup teams: {coverage.get('teams_with_posted_lineups', 0)}")

    rows_by_state = Counter(row.get('roster_state') or 'unknown' for row in rows)
    print("\nRows by roster state")
    for state in ('active', 'bench', 'available', 'unknown'):
        if rows_by_state.get(state):
            print(f"  {state}: {rows_by_state[state]}")

    actions = (decision_summary or {}).get('items') or []
    confidence_counts = Counter(action.get('context_confidence') or 'No label' for action in actions)
    kind_counts = Counter(action.get('kind') or 'UNKNOWN' for action in actions)
    print("\nAction confidence")
    if actions:
        print(f"  Actions analyzed: {len(actions)}")
        for label in ('High context', 'Medium context', 'Low context', 'No label'):
            if confidence_counts.get(label):
                print(f"  {label}: {confidence_counts[label]}/{len(actions)} ({_pct(confidence_counts[label], len(actions))})")
        print("  Action types: " + ", ".join(f"{kind} {count}" for kind, count in sorted(kind_counts.items())))
    else:
        print("  No hitter actions available.")

    blockers = []
    if coverage.get('with_lineup_spot', 0) < total:
        blockers.append('lineup spots are not fully posted yet')
    if coverage.get('with_opposing_pitcher_hand', 0) < total:
        blockers.append('opposing pitcher handedness is missing for some rows')
    if coverage.get('with_hitter_bats', 0) < total:
        blockers.append('hitter handedness is missing for some rows')
    if coverage.get('with_game_today', 0) < total:
        blockers.append('some hitters do not have a detected game today')
    print("\nMain confidence blockers")
    if blockers:
        for blocker in blockers:
            print(f"  - {blocker}")
    else:
        print("  None obvious from current context.")

    notes = summary.get('notes') or []
    if notes:
        print("\nNotes")
        for note in notes:
            print(f"  - {note}")


def _current_players_for_hitter_decisions():
    """Fetch current RoS player values/status in memory for read-only CLI output."""
    global PREVIEW_LOCAL
    old_preview = PREVIEW_LOCAL
    PREVIEW_LOCAL = True
    try:
        batters_raw = fetch_fg_ros_data('bat', 'rthebatx')
        pitchers_raw = fetch_fg_ros_data('pit', 'ratcdc')
        batters = process_fg_batters(batters_raw)
        pitchers = process_fg_pitchers(pitchers_raw)
        rankings = create_rankings(batters, pitchers)
        espn_players = fetch_espn_players()
        fg_players = rankings.to_dict('records')
        espn_matches, _ = match_fg_to_espn(fg_players, espn_players)
        roster_map = fetch_espn_rosters(load_config())
        if roster_map:
            espn_matches = reconcile_with_roster(espn_matches, roster_map, espn_players)
        players = []
        for _, row in rankings.iterrows():
            display_pos = row.get('pitcher_role', row['best_pos']) if row['type'] in ('pitcher', 'two-way') else row['best_pos']
            entry = {
                'rank': int(row['rank']),
                'name': row['name'],
                'positions': row['positions'],
                'displayPos': display_pos,
                'team': row['team'] or '',
                'dollars': round(float(row['dollars']), 1),
                'rpts': round(float(row['rpts']), 1),
                'type': row['type'],
                'fg_id': row.get('fg_id', ''),
            }
            match = espn_matches.get(row['name'])
            if match:
                entry['espn_id'] = match.get('espn_id')
            espn_id = entry.get('espn_id')
            if roster_map is None:
                entry['status'] = '?'
            elif espn_id and espn_id in roster_map:
                info = roster_map[espn_id]
                entry['status'] = 'MY ROSTER' if info.get('team_id') == ESPN_TEAM_ID else info.get('team_name', 'OTHER')
            else:
                entry['status'] = 'FA'
            players.append(entry)
        return players
    finally:
        PREVIEW_LOCAL = old_preview


def hitter_decisions():
    global PREVIEW_LOCAL
    old_preview = PREVIEW_LOCAL
    PREVIEW_LOCAL = True
    try:
        try:
            players_list = _current_players_for_hitter_decisions()
        except Exception as e:
            print(f"Current RoS hitter load failed: {type(e).__name__}: {e}")
            snapshot = load_latest_snapshot() or {}
            players_list = snapshot.get('players') or []
        if not players_list:
            print("No local tracker snapshot found; run --preview-local or a normal report first.")
        summary = build_hitter_decision_summary(
            date.today().isoformat(),
            players_list=players_list,
            matchup_snapshot_data=None,
            prediction_records=None,
            allow_live_snapshot=True,
        )
        path = write_hitter_decision_log(summary, source='hitter-decisions-cli')
        if path:
            print(f"Generated hitter decision log: {path}")
        print_hitter_decisions(summary)
        return summary
    finally:
        PREVIEW_LOCAL = old_preview


def hitter_context():
    try:
        players_list = _current_players_for_hitter_decisions()
    except Exception as e:
        print(f"Current RoS hitter load failed: {type(e).__name__}: {e}")
        players_list = (load_latest_snapshot() or {}).get('players') or []
    global PREVIEW_LOCAL
    old_preview = PREVIEW_LOCAL
    PREVIEW_LOCAL = True
    try:
        team_handedness = fetch_team_handedness()
    except Exception:
        team_handedness, _age = _load_streaming_cache('team_handedness.json', max_age_hours=168)
    snapshot = None
    try:
        snapshot = build_matchup_snapshot()
    except Exception as e:
        snapshot = {'error': f'{type(e).__name__}: {e}'}
    records, _source_kind, _source_label = _matchup_prediction_records_for_actions(date.today().isoformat(), days=6)
    try:
        context = build_hitter_daily_context(
            date.today().isoformat(),
            players_list=players_list,
            matchup_snapshot_data=snapshot,
            prediction_records=records,
            allow_live_snapshot=False,
            team_handedness_context=team_handedness,
        )
    finally:
        PREVIEW_LOCAL = old_preview
    print_hitter_context(context)
    return context


def analyze_hitter_decision_context():
    global PREVIEW_LOCAL
    old_preview = PREVIEW_LOCAL
    PREVIEW_LOCAL = True
    try:
        try:
            players_list = _current_players_for_hitter_decisions()
        except Exception as e:
            print(f"Current RoS hitter load failed: {type(e).__name__}: {e}")
            players_list = (load_latest_snapshot() or {}).get('players') or []
        if not players_list:
            print("No player list found; run --preview-local or a normal report first.")
        summary = build_hitter_decision_context_analysis(
            date.today().isoformat(),
            players_list=players_list,
        )
        print_hitter_decision_context_analysis(summary)
        return summary
    finally:
        PREVIEW_LOCAL = old_preview


def analyze_hitter_context_coverage():
    global PREVIEW_LOCAL
    old_preview = PREVIEW_LOCAL
    PREVIEW_LOCAL = True
    try:
        try:
            players_list = _current_players_for_hitter_decisions()
        except Exception as e:
            print(f"Current RoS hitter load failed: {type(e).__name__}: {e}")
            players_list = (load_latest_snapshot() or {}).get('players') or []
        if not players_list:
            print("No player list found; run --preview-local or a normal report first.")
        target_date = date.today().isoformat()
        summary = build_hitter_decision_context_analysis(
            target_date,
            players_list=players_list,
        )
        decision_summary = build_hitter_decision_summary(
            target_date,
            players_list=players_list,
            matchup_snapshot_data=None,
            prediction_records=None,
            allow_live_snapshot=True,
        )
        print_hitter_context_coverage_audit(summary, decision_summary)
        return summary
    finally:
        PREVIEW_LOCAL = old_preview


def refresh_hitter_lineups(target_date=None):
    """Refresh today's posted MLB lineup cache only; no projection changes."""
    target_date = target_date or date.today().isoformat()
    records, source_kind, source_label = _matchup_prediction_records_for_actions(target_date, days=0)
    if not any(rec.get('game_pk') for rec in records or []):
        try:
            records = fetch_weekly_schedule(target_date, target_date)
            source_kind = 'mlb_schedule'
            source_label = 'MLB schedule'
        except Exception as e:
            print(f"Unable to fetch MLB schedule for lineup refresh: {type(e).__name__}: {e}")
            records = []
    context = _fetch_hitter_lineup_context(records or [], target_date, force_refresh=True)
    players = context.get('players') or {}
    teams = context.get('teams_with_posted_lineups') or []
    game_pks = context.get('game_pks') or []
    confirmed = [
        player for player in players.values()
        if player.get('lineup_status') == 'confirmed_starting'
    ]
    print("\nHITTER LINEUP REFRESH")
    print("=" * 60)
    print("Updated local hitter lineup cache only. Scoring, predictions, learned corrections, and recommendations are unchanged.")
    print(f"Date: {target_date}")
    print(f"Schedule source: {source_label or source_kind or 'unknown'}")
    print(f"Games checked: {len(game_pks)}")
    print(f"Teams with posted lineups: {len(teams)}")
    if teams:
        print("  " + ", ".join(teams))
    else:
        print("  None yet")
    print(f"Confirmed starting hitters cached: {len(confirmed)}")
    print(f"Cache source: {context.get('source') or 'unknown'}")
    print(f"Refreshed at: {context.get('refreshed_at') or 'unknown'}")
    if not teams:
        print("Lineups may not be posted yet. Try again closer to first pitch.")
    return context


def _player_value_lookup(players_list):
    lookup = {}
    for player in players_list or []:
        name = normalize_name(player.get('name') or '')
        if name and name not in lookup:
            lookup[name] = player
    return lookup


def _ros_daily_points(player):
    """Tiny, explicit approximation for matchup edge only; not a model input."""
    if not player:
        return None
    rpts = _safe_float(player.get('rpts'))
    if rpts is None:
        return None
    # rPTS is a rest-of-season pool, not a daily hitter projection. Divide by
    # a conservative remaining-season constant so the matchup edge has a rough
    # scale without introducing a new hitter model.
    return max(rpts, 0.0) / 140.0


def _team_games_by_date(records, base_date=None, days=6):
    allowed = set(_matchup_window_dates(base_date, days))
    out = defaultdict(set)
    for rec in records or []:
        game_date = _matchup_record_date(rec)
        if game_date not in allowed:
            continue
        if rec.get('team'):
            out[rec.get('team')].add(game_date)
        if rec.get('opponent'):
            out[rec.get('opponent')].add(game_date)
    return out


def _prediction_points_by_pitcher(records):
    lookup = defaultdict(list)
    for rec in records or []:
        name = normalize_name(rec.get('name') or rec.get('pitcher_name') or '')
        if not name:
            continue
        pts = _decision_points(rec)
        lookup[name].append({
            'date': _matchup_record_date(rec),
            'points': pts,
            'opponent': rec.get('opponent'),
            'status': rec.get('status'),
        })
    return lookup


def _matchup_edge_side(rows, players_lookup, pitcher_lookup, games_by_team, base_date=None):
    projected = 0.0
    hitter_projected = 0.0
    pitcher_projected = 0.0
    projected_players = set()
    missing_players = []
    hitter_rows = [row for row in rows or [] if _matchup_player_is_hitter(row)]
    pitcher_rows = [row for row in rows or [] if _matchup_player_is_pitcher(row)]

    for row in hitter_rows:
        player = players_lookup.get(normalize_name(row.get('name') or ''))
        daily = _ros_daily_points(player)
        game_dates = games_by_team.get(row.get('team')) or set()
        if daily is not None and game_dates:
            pts = daily * len(game_dates)
            projected += pts
            hitter_projected += pts
            projected_players.add(normalize_name(row.get('name') or ''))
        else:
            missing_players.append(row.get('name') or 'Unknown hitter')

    for row in pitcher_rows:
        starts = pitcher_lookup.get(normalize_name(row.get('name') or '')) or []
        if starts:
            pts = sum(_safe_float(start.get('points')) or 0.0 for start in starts)
            projected += pts
            pitcher_projected += pts
            projected_players.add(normalize_name(row.get('name') or ''))
        else:
            missing_players.append(row.get('name') or 'Unknown pitcher')

    total_players = len(hitter_rows) + len(pitcher_rows)
    projected_count = len(projected_players)
    return {
        'remaining_points': round(projected, 1),
        'hitter_points': round(hitter_projected, 1),
        'pitcher_points': round(pitcher_projected, 1),
        'players_projected': projected_count,
        'players_missing': max(total_players - projected_count, 0),
        'players_total': total_players,
        'missing_examples': [m for m in missing_players if m][:6],
    }


def _matchup_edge_label(edge, current_margin, coverage_ratio, score_available):
    if not score_available or coverage_ratio < 0.45:
        return 'High uncertainty'
    if edge <= -10:
        return 'Chasing'
    if current_margin is not None and current_margin >= 15 and edge >= 0:
        return 'Protecting lead'
    if edge >= 10:
        return 'Slight edge'
    return 'Neutral'


def _matchup_edge_recommendations(label, edge, coverage_ratio):
    recs = []
    if label == 'Chasing':
        recs.extend([
            'Prioritize volume and upside adds where the projection is clearly positive.',
            'Borderline streamers are more defensible if they add real innings volume.',
            'Avoid low-ceiling bench bats unless they are covering a dead lineup spot.',
        ])
    elif label == 'Protecting lead':
        recs.extend([
            'Protect floor: avoid low-projection risky pitcher starts.',
            'Use obvious positive starts, but skip desperation volume.',
            'Prioritize filling active hitter slots over speculative adds.',
        ])
    elif label == 'Slight edge':
        recs.extend([
            'Take clear positive starts/adds, but avoid unnecessary volatility.',
            'Use rostered studs normally and be selective with borderline streams.',
            'Watch opponent pitcher volume before taking extra risk.',
        ])
    elif label == 'High uncertainty':
        recs.extend([
            'Confidence is low because projection coverage is incomplete.',
            'Verify active lineup slots and opponent probable starters manually.',
            'Use the detailed pitcher and hitter decision sections before making moves.',
        ])
    else:
        recs.extend([
            'Neutral posture: take clear positive starts/adds.',
            'Avoid desperation plays unless your live score falls behind.',
            'Keep active hitter slots full before chasing speculative upside.',
        ])
    if coverage_ratio < 0.7 and label != 'High uncertainty':
        recs.append('Projection coverage is incomplete, so treat the edge as a rough guide.')
    return recs[:6]


def build_matchup_edge_summary(snapshot=None, base_date=None, players_list=None,
                               prediction_records=None, limit=6, allow_live_snapshot=True):
    """Read-only rough matchup edge from ESPN score/rosters + existing projections."""
    base_date = base_date or date.today().isoformat()
    players_list = players_list or []
    if snapshot is None and allow_live_snapshot:
        snapshot = build_matchup_snapshot()
    if not snapshot or snapshot.get('error') or snapshot.get('low_confidence'):
        return {
            'available': False,
            'date': base_date,
            'label': 'High uncertainty',
            'confidence': 'low',
            'error': (snapshot or {}).get('error') or 'ESPN matchup snapshot unavailable.',
            'recommendations': _matchup_edge_recommendations('High uncertainty', 0, 0),
        }
    if prediction_records is None:
        prediction_records, _source_kind, _source_label = _matchup_prediction_records_for_actions(base_date, days=6)

    score = snapshot.get('score') or {}
    my_score = _safe_float(score.get('mine'))
    opp_score = _safe_float(score.get('opponent'))
    current_margin = _safe_float(score.get('margin'))
    score_available = my_score is not None and opp_score is not None
    players_lookup = _player_value_lookup(players_list)
    pitcher_lookup = _prediction_points_by_pitcher(prediction_records)
    games_by_team = _team_games_by_date(prediction_records, base_date, days=6)
    my_rows = (snapshot.get('my_active') or []) + (snapshot.get('my_bench') or [])
    opp_rows = (snapshot.get('opponent_active') or []) + (snapshot.get('opponent_bench') or [])
    mine = _matchup_edge_side(my_rows, players_lookup, pitcher_lookup, games_by_team, base_date)
    opponent = _matchup_edge_side(opp_rows, players_lookup, pitcher_lookup, games_by_team, base_date)
    my_remaining = mine.get('remaining_points') or 0.0
    opp_remaining = opponent.get('remaining_points') or 0.0
    my_final = (my_score or 0.0) + my_remaining if score_available else None
    opp_final = (opp_score or 0.0) + opp_remaining if score_available else None
    projected_edge = round(my_final - opp_final, 1) if my_final is not None and opp_final is not None else None
    total_players = mine.get('players_total', 0) + opponent.get('players_total', 0)
    projected_players = mine.get('players_projected', 0) + opponent.get('players_projected', 0)
    coverage_ratio = projected_players / total_players if total_players else 0.0
    label = _matchup_edge_label(projected_edge or 0.0, current_margin, coverage_ratio, score_available)
    confidence = 'medium' if coverage_ratio >= 0.7 and score_available else 'low'
    notes = [
        'Rough projection only; this is not a win probability.',
        'Hitter remaining points use current RoS rPTS as a simple daily approximation.',
    ]
    if not games_by_team:
        notes.append('Team game coverage unavailable from prediction records.')
    return {
        'available': True,
        'date': base_date,
        'my_team': (snapshot.get('my_team') or {}).get('name'),
        'opponent': (snapshot.get('opponent') or {}).get('name'),
        'scoring_period': snapshot.get('scoring_period'),
        'matchup_period': snapshot.get('matchup_period'),
        'current_score': {'mine': my_score, 'opponent': opp_score, 'margin': current_margin},
        'remaining': {'mine': my_remaining, 'opponent': opp_remaining},
        'projected_final': {
            'mine': round(my_final, 1) if my_final is not None else None,
            'opponent': round(opp_final, 1) if opp_final is not None else None,
            'edge': projected_edge,
        },
        'label': label,
        'confidence': confidence,
        'coverage': {
            'projected_players': projected_players,
            'total_players': total_players,
            'coverage_pct': round(coverage_ratio * 100, 0),
            'mine': mine,
            'opponent': opponent,
        },
        'recommendations': _matchup_edge_recommendations(label, projected_edge or 0.0, coverage_ratio)[:limit],
        'notes': notes,
    }


def print_matchup_edge(summary):
    print("\nMATCHUP EDGE")
    print("=" * 60)
    print("Read-only rough projection. This is not a win probability.")
    if not summary or not summary.get('available'):
        print(f"Unavailable: {(summary or {}).get('error') or 'unknown error'}")
        for rec in (summary or {}).get('recommendations') or []:
            print(f"  - {rec}")
        return
    score = summary.get('current_score') or {}
    remaining = summary.get('remaining') or {}
    final = summary.get('projected_final') or {}
    coverage = summary.get('coverage') or {}
    print(f"{summary.get('my_team') or 'My team'} vs {summary.get('opponent') or 'Opponent'}")
    print(f"Current score: {score.get('mine')} - {score.get('opponent')} (margin {score.get('margin')})")
    print(f"Projected remaining: mine {remaining.get('mine'):.1f}, opponent {remaining.get('opponent'):.1f}")
    print(f"Projected final: {final.get('mine')} - {final.get('opponent')} (edge {final.get('edge')})")
    print(f"Posture: {summary.get('label')} | Confidence: {summary.get('confidence')}")
    print(
        "Coverage: "
        f"{coverage.get('projected_players', 0)}/{coverage.get('total_players', 0)} players projected "
        f"({coverage.get('coverage_pct', 0):.0f}%)"
    )
    print("\nRecommendations")
    for rec in summary.get('recommendations') or []:
        print(f"  - {rec}")
    if summary.get('notes'):
        print("\nNotes")
        for note in summary.get('notes') or []:
            print(f"  - {note}")


def matchup_edge():
    players_list = []
    try:
        players_list = _current_players_for_hitter_decisions()
    except Exception as e:
        print(f"Current RoS value load failed: {type(e).__name__}: {e}")
        players_list = (load_latest_snapshot() or {}).get('players') or []
    snapshot = build_matchup_snapshot()
    records, _source_kind, _source_label = _matchup_prediction_records_for_actions(date.today().isoformat(), days=6)
    summary = build_matchup_edge_summary(
        snapshot,
        base_date=date.today().isoformat(),
        players_list=players_list,
        prediction_records=records,
        allow_live_snapshot=False,
    )
    print_matchup_edge(summary)
    return summary


def matchup_snapshot_for_report(snapshot):
    """Compact, JSON-safe matchup snapshot for the HTML report."""
    if not snapshot:
        return {'available': False, 'error': 'Matchup snapshot unavailable.'}
    if snapshot.get('error'):
        return {
            'available': False,
            'error': snapshot.get('error'),
            'available_teams': snapshot.get('available_teams') or {},
        }
    score = snapshot.get('score') or {}
    return {
        'available': True,
        'scoring_period': snapshot.get('scoring_period'),
        'matchup_period': snapshot.get('matchup_period'),
        'my_team': (snapshot.get('my_team') or {}).get('name'),
        'opponent': (snapshot.get('opponent') or {}).get('name'),
        'my_score': score.get('mine'),
        'opponent_score': score.get('opponent'),
        'margin': score.get('margin'),
        'my_active_count': len(snapshot.get('my_active') or []),
        'opponent_active_count': len(snapshot.get('opponent_active') or []),
        'injury_note_count': len(snapshot.get('injury_notes') or []),
        'empty_slots': snapshot.get('empty_slots') or {'mine': [], 'opponent': []},
        'score_fields_available': (snapshot.get('available_fields') or {}).get('score_fields', False),
    }


def daily_decision_audit(target_date=None):
    """Read-only daily pitching decision summary from existing prediction logs."""
    target_date = target_date or date.today().isoformat()
    summary = build_daily_decision_summary(target_date)
    records = summary.get('records') or []
    enrichment = summary.get('enrichment') or {}
    print("DAILY DECISION AUDIT")
    print("=" * 60)
    print("Analysis only: uses existing prediction logs and does not refresh or write data.")
    print(f"Date: {target_date}")
    print(f"Source: {summary.get('source')}")
    if not records:
        print(f"\n{summary.get('warning')}")
        return {'date': target_date, 'rows': 0}

    if enrichment['roster_status_cache_sources']:
        print("\nLocal roster/status cache sources:")
        for source in enrichment['roster_status_cache_sources']:
            print(f"  - {source}")
    elif os.path.exists(os.path.join(SCRIPT_DIR, 'espn_players.json')):
        print(
            "\nLocal ESPN player cache found, but no local ESPN roster/status cache was found; "
            "using prediction-log status history only."
        )
    else:
        print("\nNo local ESPN roster/status cache found.")

    if summary.get('warning'):
        print(
            "\nWARNING: Some roster/FA statuses are unavailable in the prediction log; "
            "roster and waiver filtering may be unreliable. To refresh statuses, run:\n"
            "  python3.11 -B engine/fantasy_tracker.py --preview-local\n"
            "or a normal tracker run."
        )

    print(f"\nRows scanned: {summary['rows_scanned']}")
    print(f"Original actionable rows: {summary['original_actionable']}")
    print(f"Rows enriched from roster/status cache: {enrichment['roster_enriched_count']}")
    print(f"Rows enriched from prediction-log status history: {enrichment['prediction_enriched_count']}")
    print(
        f"Final actionable rows: {summary['actionable_count']} "
        f"({summary['roster_count']} MY ROSTER, {summary['fa_count']} FA, {summary['waiver_count']} WAIVER)"
    )
    print(f"Hidden rows rostered by other teams / OTHER: {summary['hidden_other_count']}")
    print(f"Hidden rows still unknown or blank: {summary['hidden_unknown_count']}")
    print(f"Prediction-log status cache rows: {enrichment['prediction_status_cache_rows']}")
    print(f"Local roster/status cache rows: {enrichment['roster_status_cache_rows']}")
    print("Rostered-by-other-team rows are excluded unless they are MY ROSTER.")
    probable_sanity = summary.get('probable_sanity') or {}
    if probable_sanity.get('suppressed_total'):
        print(f"Low-confidence probable date rows hidden from decisions: {probable_sanity['suppressed_total']}")
        for ex in (probable_sanity.get('examples') or [])[:5]:
            print(
                f"  - {ex.get('pitcher')} {ex.get('date')}: {ex.get('reason')}"
            )

    _print_decision_section("Best available FA/waiver streamers today", summary['fa_ranked'], limit=8)
    _print_decision_section("My rostered starters today", summary['roster_ranked'])
    _print_decision_section("Risky rostered starts", summary['risky_roster'])
    _print_decision_section("Top avoid/trap starts among FA options", summary['avoid_traps'][:8])

    print("\nTBD/problem games")
    for item in summary['problems']:
        print(f"  - {item}")
    print("\nAnalysis only: no prediction logs, outcomes, snapshots, caches, warehouse files, or reports were written.")
    return {'date': target_date, 'rows': len(records), 'actionable': summary['actionable_count']}


def generate_tracker_html(players_list, deltas, prev_date, snapshot_date, roster_map,
                          streaming_data=None, cum_deltas=None, oldest_date=None,
                          global_emerging=None, hold_asof_label=None,
                          calibration=None, learned_candidates=None,
                          learned_biases_override=None,
                          learning_sample_summary=None,
                          feature_log_status_override=None,
                          daily_decision_summary=None,
                          next_watchlist_summary=None,
                          add_drop_priority_summary=None,
                          matchup_snapshot_summary=None,
                          matchup_action_summary=None,
                          hitter_decision_summary=None,
                          matchup_edge_summary=None,
                          decision_policy_summary=None,
                          team_handedness_context=None,
                          skip_unchanged_write=False,
                          top_banner_html=''):
    from string import Template
    if streaming_data is None:
        streaming_data = []
    if cum_deltas is None:
        cum_deltas = {}
    report_decision_records, report_decision_source = _decision_records_for_report(snapshot_date, streaming_data)
    if daily_decision_summary is None:
        decision_records = [
            rec for rec in report_decision_records
            if (rec.get('date') or rec.get('game_date')) == snapshot_date
        ]
        if decision_records:
            daily_decision_summary = decision_summary_for_report(
                build_daily_decision_summary(snapshot_date, records=decision_records, source=report_decision_source)
            )
        else:
            daily_decision_summary = decision_summary_for_report(build_daily_decision_summary(snapshot_date))
    if next_watchlist_summary is None:
        if report_decision_records:
            next_watchlist_summary = build_next_watchlist_summary(
                snapshot_date, records=report_decision_records, source=report_decision_source
            )
        else:
            next_watchlist_summary = build_next_watchlist_summary(snapshot_date)
    if add_drop_priority_summary is None:
        add_drop_priority_summary = build_add_drop_priority_summary(
            snapshot_date, daily_decision_summary, next_watchlist_summary
        )
    if decision_policy_summary is None:
        try:
            decision_policy_summary = build_start_sit_policy_backtest_summary()
        except Exception as e:
            decision_policy_summary = {
                'available': False,
                'note': f'Decision policy backtest unavailable: {type(e).__name__}: {e}',
            }
    matchup_snapshot_data = None
    if matchup_snapshot_summary is None or matchup_action_summary is None:
        try:
            matchup_snapshot_data = build_matchup_snapshot()
            if matchup_snapshot_summary is None:
                matchup_snapshot_summary = matchup_snapshot_for_report(matchup_snapshot_data)
            if matchup_action_summary is None:
                matchup_action_summary = build_matchup_action_recommendations(
                    matchup_snapshot_data,
                    base_date=snapshot_date,
                    prediction_records=report_decision_records,
                    prediction_source=report_decision_source,
                )
        except Exception as e:
            matchup_snapshot_summary = {
                'available': False,
                'error': f'Matchup data unavailable: {type(e).__name__}',
            }
            matchup_action_summary = {
                'date': snapshot_date,
                'items': [],
                'count': 0,
                'notes': [f'Matchup actions unavailable: {type(e).__name__}: {e}'],
            }

    # Build a lookup of emerging (HOLD) pitchers.
    # Prefer the global emerging map (assesses ALL FA + MY ROSTER SPs by recent form,
    # whether or not they have an upcoming scheduled start). Fall back to deriving
    # from streaming_data if the global map wasn't supplied.
    if global_emerging is not None:
        emerging_pitchers = set(global_emerging)
    else:
        emerging_pitchers = set()
        for s in streaming_data:
            if s.get('emerging') and s.get('name') and s.get('name') != 'TBD':
                emerging_pitchers.add(normalize_name(s['name']))

    # Enrich player data with deltas and status
    for p in players_list:
        fg_id = p.get('fg_id', '')
        key = fg_id or p['name']
        delta = deltas.get(key, {})
        p['dollarChange'] = delta.get('dollar_change')
        p['rptsChange'] = delta.get('rpts_change')
        p['rankChange'] = delta.get('rank_change')
        # Cumulative changes from oldest snapshot
        cum = cum_deltas.get(key, {})
        p['totalChange'] = cum.get('total_dollar_change')
        p['totalRankChange'] = cum.get('total_rank_change')
        # HOLD designation from streaming analysis
        p['emerging'] = normalize_name(p['name']) in emerging_pitchers

        espn_id = p.get('espn_id')
        if roster_map is None:
            p['status'] = '?'
        elif espn_id and espn_id in roster_map:
            info = roster_map[espn_id]
            if info['team_id'] == ESPN_TEAM_ID:
                p['status'] = 'MY ROSTER'
            else:
                p['status'] = info['team_name']
        else:
            p['status'] = 'FA'

    my_roster_count = sum(1 for p in players_list if p.get('status') == 'MY ROSTER')
    fa_count = sum(1 for p in players_list if p.get('status') == 'FA')
    risers = sum(1 for p in players_list if (p.get('dollarChange') or 0) > 0.5)
    fallers = sum(1 for p in players_list if (p.get('dollarChange') or 0) < -0.5)
    trending_up = sum(1 for p in players_list if (p.get('totalChange') or 0) > 1.0 and p.get('dollars', 0) >= -5)
    if hitter_decision_summary is None:
        try:
            hitter_decision_summary = build_hitter_decision_summary(
                snapshot_date,
                players_list=players_list,
                matchup_snapshot_data=matchup_snapshot_data,
                prediction_records=report_decision_records,
                allow_live_snapshot=matchup_snapshot_data is None and matchup_snapshot_summary is None,
                team_handedness_context=team_handedness_context,
            )
        except Exception as e:
            hitter_decision_summary = {
                'date': snapshot_date,
                'items': [],
                'count': 0,
                'notes': [f'Hitter decisions unavailable: {type(e).__name__}: {e}'],
                'data_available': {'ros_values': bool(players_list), 'espn_roster': False, 'team_game_schedule': False},
            }
    try:
        write_hitter_decision_log(hitter_decision_summary, source='html-report')
    except Exception as e:
        print(f"  Hitter decision log skipped: {type(e).__name__}: {e}")
    if matchup_edge_summary is None:
        try:
            matchup_edge_summary = build_matchup_edge_summary(
                matchup_snapshot_data,
                base_date=snapshot_date,
                players_list=players_list,
                prediction_records=report_decision_records,
                allow_live_snapshot=matchup_snapshot_data is None and matchup_snapshot_summary is None,
            )
        except Exception as e:
            matchup_edge_summary = {
                'available': False,
                'date': snapshot_date,
                'label': 'High uncertainty',
                'confidence': 'low',
                'error': f'Matchup edge unavailable: {type(e).__name__}: {e}',
                'recommendations': _matchup_edge_recommendations('High uncertainty', 0, 0),
            }
    prev_label = f"vs {prev_date}" if prev_date else "first snapshot"
    oldest_label = oldest_date or prev_date or "N/A"

    html_template = Template(r"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>Fantasy Tracker</title>
<style>
* { box-sizing: border-box; margin: 0; padding: 0; }
body { font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Roboto, sans-serif; background: #0a0a0f; color: #e0e0e0; }
.header { background: linear-gradient(135deg, #1a1a2e 0%, #16213e 100%); padding: 20px 30px; border-bottom: 3px solid #3b82f6; }
.header h1 { font-size: 24px; color: #fff; }
.header .subtitle { color: #888; font-size: 13px; margin-top: 4px; }
.preview-banner { padding: 12px 30px; background: #3a2500; color: #fef3c7; border-bottom: 1px solid #a16207; font-size: 13px; line-height: 1.45; }
.preview-banner b { color: #fff7ed; }
.preview-banner .meta { color: #fde68a; font-size: 12px; margin-top: 2px; }
.tab-bar { display: flex; gap: 0; margin-top: 14px; }
.tab-btn { padding: 8px 24px; border: none; background: transparent; color: #666; cursor: pointer; font-size: 14px; font-weight: 500; border-bottom: 2px solid transparent; transition: all 0.15s; }
.tab-btn:hover { color: #aaa; }
.tab-btn.active { color: #fff; border-bottom-color: #3b82f6; }
.tab-view { display: none; }
.tab-view.active { display: block; }
.controls { display: flex; flex-wrap: wrap; gap: 10px; align-items: center; padding: 15px 30px; background: #111118; border-bottom: 1px solid #222; }
.search-box { padding: 8px 14px; border: 1px solid #333; border-radius: 6px; background: #1a1a24; color: #e0e0e0; font-size: 14px; width: 240px; }
.search-box:focus { outline: none; border-color: #3b82f6; }
.filter-btns { display: flex; flex-wrap: wrap; gap: 4px; }
.filter-btn { padding: 5px 12px; border: 1px solid #333; border-radius: 4px; background: #1a1a24; color: #aaa; cursor: pointer; font-size: 12px; font-weight: 500; transition: all 0.15s; }
.filter-btn:hover { border-color: #555; color: #fff; }
.filter-btn.active { background: #3b82f6; border-color: #3b82f6; color: #fff; }
.filter-btn.active-pos { background: #059669; border-color: #059669; color: #fff; }
.stats-bar { display: flex; gap: 20px; padding: 10px 30px; background: #0d0d14; border-bottom: 1px solid #1a1a24; font-size: 12px; color: #666; flex-wrap: wrap; }
.stats-bar .stat { display: flex; gap: 4px; }
.stats-bar .stat-label { color: #555; }
.stats-bar .stat-value { color: #aaa; font-weight: 500; }
.table-wrap { overflow-x: auto; }
table { width: 100%; border-collapse: collapse; font-size: 13px; }
thead { position: sticky; top: 0; z-index: 10; }
th { background: #16161f; padding: 10px 12px; text-align: left; font-weight: 600; color: #888; border-bottom: 2px solid #3b82f6; cursor: pointer; user-select: none; white-space: nowrap; }
th:hover { color: #fff; }
th.sorted-asc::after { content: ' \25B2'; font-size: 10px; }
th.sorted-desc::after { content: ' \25BC'; font-size: 10px; }
td { padding: 8px 12px; border-bottom: 1px solid #1a1a24; white-space: nowrap; }
tr:hover { background: #1a1a28 !important; }
tr.row-mine { background: rgba(251, 191, 36, 0.08); border-left: 3px solid #fbbf24; }
tr.row-mine:hover { background: rgba(251, 191, 36, 0.14) !important; }
.rank-cell { text-align: center; font-weight: 600; color: #888; min-width: 40px; }
.name-cell { font-weight: 500; color: #fff; min-width: 180px; }
.pos-cell { min-width: 40px; }
.pos-sp { color: #4ade80; }
.pos-rp { color: #a78bfa; }
.pos-hitter { color: #60a5fa; }
.team-cell { color: #777; min-width: 50px; }
.num-cell { text-align: right; font-variant-numeric: tabular-nums; min-width: 65px; }
.dollars-pos { color: #34d399; }
.dollars-neg { color: #ef4444; }
.change-pos { color: #34d399; font-weight: 500; }
.change-neg { color: #ef4444; font-weight: 500; }
.change-none { color: #555; }
.status-mine { color: #fbbf24; font-weight: 600; }
.status-fa { color: #4ade80; }
.row-hold { display: inline-block; margin-left: 6px; padding: 1px 6px; border-radius: 3px; background: rgba(168,85,247,0.2); color: #c084fc; font-size: 10px; font-weight: 600; vertical-align: middle; }
.status-other { color: #555; font-size: 11px; }
.no-results { padding: 40px; text-align: center; color: #555; font-size: 15px; }
.pos-hint { padding: 8px 30px; background: #0d0d14; color: #666; font-size: 12px; border-bottom: 1px solid #1a1a24; display: none; }
/* Streaming styles */
.day-card { margin: 12px 20px; background: #111118; border-radius: 8px; border: 1px solid #222; overflow: hidden; }
.day-header { padding: 10px 16px; background: #16161f; display: flex; justify-content: space-between; align-items: center; }
.day-date { color: #fff; font-weight: 600; font-size: 14px; }
.day-count { color: #666; font-size: 12px; }
.stream-entry { padding: 10px 16px; border-bottom: 1px solid #1a1a24; }
.stream-entry:last-child { border-bottom: none; }
.stream-entry.stream-mine { background: rgba(251, 191, 36, 0.06); border-left: 3px solid #fbbf24; }
.stream-entry.stream-top { border-left: 3px solid #34d399; }
.stream-row1 { display: flex; align-items: center; gap: 12px; flex-wrap: wrap; }
.stream-name { font-weight: 600; color: #fff; min-width: 160px; }
.stream-name .star { color: #34d399; margin-right: 4px; }
.stream-team { color: #777; font-size: 12px; min-width: 36px; }
.stream-matchup { color: #aaa; font-size: 13px; min-width: 80px; }
.stream-pts { font-weight: 700; font-size: 15px; min-width: 70px; text-align: right; }
.stream-pts.pts-good { color: #34d399; }
.stream-pts.pts-ok { color: #fbbf24; }
.stream-pts.pts-bad { color: #ef4444; }
.stream-stat { color: #888; font-size: 12px; }
.stream-stat b { color: #ccc; }
.chip { display: inline-block; padding: 1px 7px; border-radius: 3px; font-size: 10px; font-weight: 700; letter-spacing: 0.5px; margin-left: 6px; }
.chip-ace { background: rgba(52, 211, 153, 0.2); color: #34d399; }
.chip-safe { background: rgba(96, 165, 250, 0.2); color: #60a5fa; }
.chip-upside { background: rgba(251, 146, 60, 0.2); color: #fb923c; }
.chip-mine { background: rgba(251, 191, 36, 0.15); color: #fbbf24; font-size: 9px; }
.stream-row2 { display: flex; gap: 8px; flex-wrap: wrap; margin-top: 4px; font-size: 11px; color: #666; align-items: center; }
.stream-row2 span { display: inline-flex; align-items: center; gap: 2px; }
.opp-easy { color: #34d399; }
.opp-mid { color: #888; }
.opp-hard { color: #ef4444; }
.trend-hot { color: #34d399; }
.trend-cold { color: #ef4444; }
.platoon-edge { color: #34d399; }
.platoon-risk { color: #fb923c; }
.stream-tbd { padding: 10px 16px; color: #555; font-style: italic; font-size: 13px; }
.stream-note { padding: 10px 20px; color: #555; font-size: 12px; }
.stream-legend { padding: 0 20px 10px; color: #777; font-size: 11px; line-height: 1.45; border-bottom: 1px solid #1a1a24; }
.stream-explain { margin-top: 7px; padding: 7px 9px; border-radius: 6px; background: #0d0d14; border: 1px solid #20202a; color: #aaa; font-size: 12px; line-height: 1.4; }
.stream-explain b { color: #ddd; font-weight: 700; }
.stream-explain .why-start { color: #86efac; }
.stream-explain .why-borderline { color: #fbbf24; }
.stream-explain .why-sit { color: #fca5a5; }
.stream-caution { margin-top: 7px; padding: 7px 9px; border-radius: 6px; background: rgba(251,191,36,0.08); border: 1px solid rgba(251,191,36,0.28); color: #fcd34d; font-size: 12px; line-height: 1.4; }
.stream-caution b { color: #fde68a; }
.decision-card { margin-top: 8px; }
.decision-summary { padding: 10px 16px; display: flex; gap: 8px; flex-wrap: wrap; align-items: center; border-bottom: 1px solid #1a1a24; }
.decision-pill { display: inline-flex; gap: 4px; align-items: center; padding: 3px 8px; border-radius: 999px; background: #1a1a24; border: 1px solid #2a2a35; color: #aaa; font-size: 11px; }
.decision-pill b { color: #fff; }
.decision-warning { margin: 8px 16px 0; padding: 8px 10px; border-radius: 6px; background: rgba(251,191,36,0.08); border: 1px solid rgba(251,191,36,0.28); color: #fbbf24; font-size: 12px; }
.decision-grid { padding: 10px 16px 14px; display: grid; grid-template-columns: repeat(auto-fit, minmax(230px, 1fr)); gap: 10px; }
.decision-section { background: #0d0d14; border: 1px solid #20202a; border-radius: 6px; overflow: hidden; }
.decision-section-title { padding: 7px 9px; background: #16161f; color: #ddd; font-size: 11px; font-weight: 700; letter-spacing: 0.4px; text-transform: uppercase; }
.decision-row { padding: 8px 9px; border-top: 1px solid #1a1a24; }
.decision-row:first-child { border-top: none; }
.decision-line1 { display: flex; justify-content: space-between; gap: 8px; align-items: baseline; }
.decision-name { color: #fff; font-weight: 600; font-size: 13px; min-width: 0; overflow: hidden; text-overflow: ellipsis; white-space: nowrap; }
.decision-pts { color: #34d399; font-weight: 700; font-size: 13px; white-space: nowrap; }
.decision-meta { margin-top: 3px; color: #888; font-size: 11px; }
.decision-notes { margin-top: 4px; color: #777; font-size: 11px; line-height: 1.35; }
.decision-reasons { margin-top: 5px; color: #aaa; font-size: 11px; line-height: 1.35; display: grid; gap: 2px; }
.decision-reason-label { color: #777; font-weight: 700; text-transform: uppercase; font-size: 9px; letter-spacing: 0.4px; margin-right: 5px; }
.decision-overlap { display: inline-block; margin-top: 4px; color: #777; font-size: 10px; }
.decision-risk { color: #fca5a5; }
.decision-boost { color: #86efac; }
.decision-confidence { color: #ddd; font-weight: 700; }
.decision-confidence.conf-strong { color: #34d399; }
.decision-confidence.conf-start { color: #60a5fa; }
.decision-confidence.conf-borderline { color: #fbbf24; }
.decision-confidence.conf-avoid { color: #f87171; }
.decision-empty { padding: 10px 9px; color: #555; font-size: 12px; }
.decision-compact-list { display: grid; }
.decision-compact-row { padding: 7px 9px; border-top: 1px solid #1a1a24; display: grid; grid-template-columns: minmax(92px, 1.2fr) auto minmax(86px, 1fr); gap: 7px; align-items: center; }
.decision-compact-row:first-child { border-top: none; }
.decision-compact-main { min-width: 0; }
.decision-compact-meta { color: #888; font-size: 11px; white-space: nowrap; }
.decision-compact-risk { color: #fca5a5; font-size: 11px; line-height: 1.3; min-width: 0; overflow: hidden; text-overflow: ellipsis; white-space: nowrap; }
.decision-compact-risk .decision-overlap { margin: 0 0 0 6px; }
.watch-label { display: inline-block; margin-right: 7px; margin-bottom: 2px; padding: 1px 5px; border-radius: 3px; background: #1a1a24; color: #aaa; border: 1px solid #2a2a35; font-size: 9px; font-weight: 700; letter-spacing: 0.3px; vertical-align: baseline; }
.watch-day { border-top: 1px solid #1a1a24; }
.watch-day:first-child { border-top: none; }
.watch-date { padding: 8px 16px 0; color: #ddd; font-size: 12px; font-weight: 700; }
.watch-grid { padding-top: 8px; }
.action-list { padding: 10px 16px 14px; display: grid; gap: 7px; }
.action-row { display: grid; grid-template-columns: auto 1fr auto; gap: 8px; align-items: center; padding: 8px 9px; border: 1px solid #20202a; border-radius: 6px; background: #0d0d14; }
.action-kind { padding: 2px 6px; border-radius: 3px; background: #1a1a24; color: #ddd; border: 1px solid #2a2a35; font-size: 9px; font-weight: 800; letter-spacing: 0.4px; }
.action-kind.lock-in { color: #34d399; border-color: rgba(52,211,153,0.45); background: rgba(52,211,153,0.1); }
.action-kind.add, .action-kind.start { color: #34d399; border-color: rgba(52,211,153,0.4); background: rgba(52,211,153,0.08); }
.action-kind.consider, .action-kind.watch { color: #fbbf24; border-color: rgba(251,191,36,0.35); background: rgba(251,191,36,0.08); }
.action-kind.bench, .action-kind.avoid, .action-kind.desperation, .action-kind.injury-check, .action-kind.no-game { color: #f87171; border-color: rgba(248,113,113,0.35); background: rgba(248,113,113,0.08); }
.action-text { color: #e5e7eb; font-size: 12px; line-height: 1.35; min-width: 0; }
.action-meta { color: #888; font-size: 11px; white-space: nowrap; }
.matchup-grid { padding: 10px 16px 14px; display: grid; grid-template-columns: minmax(230px, 0.8fr) minmax(280px, 1.2fr); gap: 10px; }
.matchup-score { font-size: 20px; color: #fff; font-weight: 800; margin-top: 4px; }
.matchup-margin { font-size: 13px; font-weight: 700; }
.matchup-margin.good { color: #34d399; }
.matchup-margin.bad { color: #f87171; }
.matchup-small { color: #888; font-size: 12px; line-height: 1.45; margin-top: 6px; }
.accuracy-card { margin: 8px 0; }
.accuracy-stats { padding: 14px 16px; display: flex; gap: 32px; flex-wrap: wrap; font-size: 13px; }
.accuracy-stat { min-width: 92px; }
.accuracy-table-wrap { padding: 8px 0; overflow-x: auto; -webkit-overflow-scrolling: touch; }
.accuracy-table { width: 100%; min-width: 520px; font-size: 13px; border-collapse: collapse; }
.accuracy-list { padding: 6px 16px; }
.accuracy-row { padding: 7px 0; border-bottom: 1px solid #1a1a1a; display: flex; justify-content: space-between; gap: 12px; font-size: 13px; }
.accuracy-row-main { min-width: 0; }
.accuracy-row-detail { text-align: right; color: #aaa; white-space: nowrap; }
.accuracy-detail { color: #777; font-size: 11px; margin-top: 2px; line-height: 1.35; overflow-wrap: anywhere; }
@media (max-width: 720px) { .action-row { grid-template-columns: 1fr; gap: 4px; } .action-meta { white-space: normal; } }
@media (max-width: 820px) { .matchup-grid { grid-template-columns: 1fr; } }
@media (max-width: 640px) {
  .header { padding: 16px 18px; }
  .tab-bar { overflow-x: auto; }
  .tab-btn { padding: 8px 14px; white-space: nowrap; }
  .stream-note, .stream-legend { padding-left: 14px; padding-right: 14px; }
  .day-card { margin-left: 10px; margin-right: 10px; }
  .day-header { gap: 10px; align-items: flex-start; }
  .day-header span:last-child { text-align: right; }
  .accuracy-stats { gap: 14px; padding: 12px 14px; }
  .accuracy-stat { flex: 1 1 120px; }
  .accuracy-list { padding: 6px 12px; }
  .accuracy-row { display: block; }
  .accuracy-row-detail { margin-top: 3px; text-align: left; white-space: normal; }
  .accuracy-detail { font-size: 10.5px; }
}
.tier-header { padding: 6px 16px; font-size: 11px; font-weight: 700; letter-spacing: 0.8px; text-transform: uppercase; border-top: 1px solid #222; }
.tier-header:first-child { border-top: none; }
.tier-must_start { color: #34d399; background: rgba(52,211,153,0.05); }
.tier-start { color: #60a5fa; background: rgba(96,165,250,0.05); }
.tier-borderline { color: #fbbf24; background: rgba(251,191,36,0.05); }
.tier-avoid { color: #ef4444; background: rgba(239,68,68,0.05); }
.stream-row3 { margin-top: 4px; font-size: 11px; color: #777; }
.pitch-bar { display: flex; gap: 6px; flex-wrap: wrap; align-items: center; }
.pitch-pill { display: inline-flex; align-items: center; gap: 4px; padding: 2px 8px; border-radius: 4px; background: #1a1a24; border: 1px solid #2a2a35; font-size: 10px; }
.pitch-pill .pitch-name { color: #ccc; font-weight: 600; }
.pitch-pill .pitch-detail { color: #888; }
.pitch-pill.pitch-elite { border-color: #34d399; background: rgba(52,211,153,0.08); }
.pitch-pill.pitch-plus { border-color: #60a5fa; background: rgba(96,165,250,0.06); }
.pitch-pill.pitch-weak { border-color: #ef4444; background: rgba(239,68,68,0.06); }
.pitch-matchup-strong { color: #34d399; }
.pitch-matchup-favorable { color: #6ee7b7; }
.pitch-matchup-poor { color: #ef4444; }
.pitch-matchup-unfavorable { color: #fca5a5; }
.pitch-summary { color: #999; font-style: italic; margin-left: 4px; }
.park-boost { color: #34d399; font-size: 10px; font-weight: 600; }
.park-penalty { color: #ef4444; font-size: 10px; font-weight: 600; }
.opp-il-boost { color: #34d399; font-size: 10px; font-weight: 600; }
.opp-il-warn { color: #f59e0b; font-size: 10px; font-weight: 600; }
.chip-emerging { background: rgba(168,85,247,0.2); color: #c084fc; }
.adj-chip { display: inline-flex; align-items: center; gap: 3px; font-size: 10px; padding: 2px 6px; margin-left: 6px; border-radius: 10px; cursor: help; font-weight: 600; vertical-align: middle; }
.adj-up { background: rgba(52,211,153,0.18); color: #34d399; border: 1px solid rgba(52,211,153,0.35); }
.adj-down { background: rgba(239,68,68,0.18); color: #f87171; border: 1px solid rgba(239,68,68,0.35); }
.adj-chip::before { content: '\2728'; font-size: 8px; }
</style>
</head>
<body>

<div class="header">
  <h1>Fantasy In-Season Tracker</h1>
  <div class="subtitle">Snapshot: $SNAPSHOT_DATE ($PREV_LABEL) &bull; RoS Projections &bull; THE BAT X RoS (bat) + ATC DC RoS (pit)</div>
  <div class="tab-bar">
    <button class="tab-btn active" data-tab="tracker">RoS Tracker</button>
    <button class="tab-btn" data-tab="streaming">Streaming</button>
    <button class="tab-btn" data-tab="decisions">Decisions</button>
    <button class="tab-btn" data-tab="accuracy">Accuracy</button>
  </div>
</div>
$TOP_BANNER_HTML

<!-- ===== RoS TRACKER TAB ===== -->
<div class="tab-view active" id="tab-tracker">

<div class="controls">
  <input type="text" class="search-box" id="search" placeholder="Search player name...">
  <div class="filter-btns" id="statusFilters">
    <button class="filter-btn active" data-filter="all">All</button>
    <button class="filter-btn" data-filter="roster">My Roster</button>
    <button class="filter-btn" data-filter="fa">Free Agents</button>
    <button class="filter-btn" data-filter="risers">Risers</button>
    <button class="filter-btn" data-filter="fallers">Fallers</button>
    <button class="filter-btn" data-filter="trending">Trending</button>
    <button class="filter-btn" data-filter="holds">Holds</button>
  </div>
  <div class="filter-btns" id="posFilters">
    <button class="filter-btn active-pos" data-pos="all">All Pos</button>
    <span style="width:1px;background:#333;margin:0 4px"></span>
    <button class="filter-btn" data-pos="C">C</button>
    <button class="filter-btn" data-pos="1B">1B</button>
    <button class="filter-btn" data-pos="2B">2B</button>
    <button class="filter-btn" data-pos="3B">3B</button>
    <button class="filter-btn" data-pos="SS">SS</button>
    <button class="filter-btn" data-pos="OF">OF</button>
    <span style="width:1px;background:#333;margin:0 4px"></span>
    <button class="filter-btn" data-pos="SP">SP</button>
    <button class="filter-btn" data-pos="RP">RP</button>
  </div>
</div>

<div class="stats-bar">
  <div class="stat"><span class="stat-label">My Roster:</span><span class="stat-value">$MY_ROSTER_COUNT</span></div>
  <div class="stat"><span class="stat-label">Free Agents:</span><span class="stat-value">$FA_COUNT</span></div>
  <div class="stat"><span class="stat-label">Risers:</span><span class="stat-value">$RISERS</span></div>
  <div class="stat"><span class="stat-label">Fallers:</span><span class="stat-value">$FALLERS</span></div>
  <div class="stat"><span class="stat-label">Trending (since $OLDEST_DATE):</span><span class="stat-value">$TRENDING</span></div>
</div>

<div class="pos-hint" id="posHint"></div>

<div class="table-wrap">
<table>
  <thead>
    <tr>
      <th data-sort="rank" class="sorted-asc">Rank</th>
      <th data-sort="name">Player</th>
      <th data-sort="displayPos">Pos</th>
      <th data-sort="team">Team</th>
      <th data-sort="dollars">$$</th>
      <th data-sort="dollarChange">$$ Chg</th>
      <th data-sort="totalChange">Total Chg</th>
      <th data-sort="rpts">rPTS</th>
      <th data-sort="status">Status</th>
    </tr>
  </thead>
  <tbody id="tbody"></tbody>
</table>
<div class="no-results" id="noResults" style="display:none">No players match your search/filter.</div>
</div>

</div><!-- end tab-tracker -->

<!-- ===== STREAMING TAB ===== -->
<div class="tab-view" id="tab-streaming">
<div class="stream-note">Streaming: $WEEK_RANGE (5-day look-ahead) &bull; Sorted by projected pts/start &bull; Your starters highlighted in gold</div>
<div class="stream-legend">Pitch pills: green/blue/red borders show pitch quality; arrows show matchup fit vs today&rsquo;s opponent (up = favorable, down = risk). HOT/COLD compares last-14-day ERA to projection; COLD means recent ERA is at least 1.5 runs worse.</div>
<div id="streamContent"></div>
</div><!-- end tab-streaming -->

<!-- ===== DECISIONS TAB ===== -->
<div class="tab-view" id="tab-decisions">
<div class="stream-note">Quick decision tools for matchup context, roster checks, add/drop planning, and watchlist review. The main Streaming tab stays focused on the regular projection list.</div>
<div id="matchupContent"></div>
<div id="matchupEdgeContent"></div>
<div id="hitterDecisionContent"></div>
<div id="decisionContent"></div>
<div id="addDropContent"></div>
<div id="watchlistContent"></div>
</div><!-- end tab-decisions -->

<!-- ===== ACCURACY TAB ===== -->
<div class="tab-view" id="tab-accuracy">
<div class="stream-note">How well are predictions tracking actual results? Every scheduled SP gets logged each run; outcomes get joined the next morning. As more data accrues, we'll see which features the model is over/under-weighting.</div>
<div class="stream-note">Workload and weather/roof features are currently logged for learning and audit only. They do not directly change projected points unless the learned-correction system later activates a statistically safe bucket. $FEATURE_LOG_STATUS</div>
<div id="accuracyContent"></div>
</div><!-- end tab-accuracy -->

<script>
var PLAYERS = $PLAYERS_JSON;
var STREAMING = $STREAMING_JSON;
var CALIBRATION = $CALIBRATION_JSON;
var LEARNED_BIASES = $LEARNED_BIASES_JSON;
var LEARNED_CANDIDATES = $LEARNED_CANDIDATES_JSON;
var LEARNING_SAMPLE_SUMMARY = $LEARNING_SAMPLE_SUMMARY_JSON;
var DECISION_POLICY_BACKTEST = $DECISION_POLICY_BACKTEST_JSON;
var DAILY_DECISIONS = $DAILY_DECISIONS_JSON;
var NEXT_WATCHLIST = $NEXT_WATCHLIST_JSON;
var ADD_DROP_PRIORITY = $ADD_DROP_PRIORITY_JSON;
var MATCHUP_SNAPSHOT = $MATCHUP_SNAPSHOT_JSON;
var MATCHUP_ACTIONS = $MATCHUP_ACTIONS_JSON;
var HITTER_DECISIONS = $HITTER_DECISIONS_JSON;
var MATCHUP_EDGE = $MATCHUP_EDGE_JSON;

/* ===== RoS Tracker logic ===== */
var statusFilter = 'all';
var posFilter = 'all';
var currentSearch = '';
var sortCol = 'rank';
var sortAsc = true;

function hasPos(r, pos) {
  if (pos === 'SP' || pos === 'RP') return r.pitcherRole === pos || r.displayPos === pos;
  return r.positions && r.positions.indexOf(pos) !== -1;
}

function getFiltered() {
  var data = PLAYERS;
  if (posFilter !== 'all') {
    data = data.filter(function(r) { return hasPos(r, posFilter); });
    if (statusFilter === 'all') {
      data = data.filter(function(r) { return r.status === 'MY ROSTER' || r.status === 'FA'; });
    }
  }
  if (statusFilter === 'roster') data = data.filter(function(r) { return r.status === 'MY ROSTER'; });
  else if (statusFilter === 'fa') data = data.filter(function(r) { return r.status === 'FA'; });
  else if (statusFilter === 'risers') data = data.filter(function(r) { return r.dollarChange !== null && r.dollarChange > 0.5; });
  else if (statusFilter === 'fallers') data = data.filter(function(r) { return r.dollarChange !== null && r.dollarChange < -0.5; });
  else if (statusFilter === 'trending') data = data.filter(function(r) { return r.totalChange !== null && r.totalChange > 1.0 && r.dollars >= -5; });
  else if (statusFilter === 'holds') data = data.filter(function(r) { return r.emerging; });
  if (currentSearch) {
    var q = currentSearch.toLowerCase().normalize('NFD').replace(/[\u0300-\u036f]/g, '');
    data = data.filter(function(r) { return r.name.toLowerCase().normalize('NFD').replace(/[\u0300-\u036f]/g, '').indexOf(q) !== -1; });
  }
  data = data.slice().sort(function(a, b) {
    var va = a[sortCol], vb = b[sortCol];
    if (va === null || va === undefined) va = sortAsc ? 99999 : -99999;
    if (vb === null || vb === undefined) vb = sortAsc ? 99999 : -99999;
    if (typeof va === 'string') { va = va.toLowerCase(); vb = (vb||'').toLowerCase(); }
    if (va < vb) return sortAsc ? -1 : 1;
    if (va > vb) return sortAsc ? 1 : -1;
    return 0;
  });
  return data;
}

function fmtChange(v) {
  if (v === null || v === undefined) return '<span class="change-none">--</span>';
  if (v > 0) return '<span class="change-pos">+' + v.toFixed(1) + '</span>';
  if (v < 0) return '<span class="change-neg">' + v.toFixed(1) + '</span>';
  return '<span class="change-none">0.0</span>';
}

function fmtStatus(s) {
  if (s === 'MY ROSTER') return '<span class="status-mine">MY ROSTER</span>';
  if (s === 'FA') return '<span class="status-fa">FA</span>';
  if (s === '?') return '<span class="change-none">?</span>';
  return '<span class="status-other">' + s + '</span>';
}

function render() {
  var data = getFiltered();
  var tbody = document.getElementById('tbody');
  var noRes = document.getElementById('noResults');
  var hint = document.getElementById('posHint');
  if (data.length === 0) { tbody.innerHTML = ''; noRes.style.display = 'block'; hint.style.display = 'none'; return; }
  noRes.style.display = 'none';
  if (posFilter !== 'all' && statusFilter === 'all') {
    var myCount = data.filter(function(r) { return r.status === 'MY ROSTER'; }).length;
    var faCount = data.filter(function(r) { return r.status === 'FA'; }).length;
    hint.textContent = posFilter + ': ' + myCount + ' on your roster, ' + faCount + ' free agents \u2014 your players highlighted';
    hint.style.display = 'block';
  } else { hint.style.display = 'none'; }
  tbody.innerHTML = data.map(function(r) {
    var posClass = r.displayPos === 'SP' ? 'pos-sp' : r.displayPos === 'RP' ? 'pos-rp' : 'pos-hitter';
    var dollarClass = r.dollars > 0 ? 'dollars-pos' : 'dollars-neg';
    var rowClass = r.status === 'MY ROSTER' ? ' class="row-mine"' : '';
    return '<tr' + rowClass + '>' +
      '<td class="rank-cell">' + r.rank + '</td>' +
      '<td class="name-cell">' + r.name + (r.emerging ? ' <span class="row-hold" title="Based on L14D stats through $HOLD_ASOF">HOLD</span>' : '') + '</td>' +
      '<td class="pos-cell ' + posClass + '">' + r.displayPos + '</td>' +
      '<td class="team-cell">' + r.team + '</td>' +
      '<td class="num-cell ' + dollarClass + '">$$' + r.dollars.toFixed(1) + '</td>' +
      '<td class="num-cell">' + fmtChange(r.dollarChange) + '</td>' +
      '<td class="num-cell">' + fmtChange(r.totalChange) + '</td>' +
      '<td class="num-cell" style="color:#fbbf24">' + r.rpts.toFixed(1) + '</td>' +
      '<td>' + fmtStatus(r.status) + '</td>' +
      '</tr>';
  }).join('');
}

document.getElementById('statusFilters').addEventListener('click', function(e) {
  if (!e.target.classList.contains('filter-btn')) return;
  e.target.parentElement.querySelectorAll('.filter-btn').forEach(function(b) { b.classList.remove('active'); });
  e.target.classList.add('active');
  statusFilter = e.target.dataset.filter;
  if (statusFilter === 'risers') { sortCol = 'dollarChange'; sortAsc = false; }
  else if (statusFilter === 'fallers') { sortCol = 'dollarChange'; sortAsc = true; }
  else if (statusFilter === 'trending') { sortCol = 'totalChange'; sortAsc = false; }
  else if (statusFilter === 'holds') { sortCol = 'rank'; sortAsc = true; }
  else { sortCol = 'rank'; sortAsc = true; }
  render();
});

document.getElementById('posFilters').addEventListener('click', function(e) {
  if (!e.target.classList.contains('filter-btn')) return;
  e.target.parentElement.querySelectorAll('.filter-btn').forEach(function(b) { b.classList.remove('active-pos'); });
  e.target.classList.add('active-pos');
  posFilter = e.target.dataset.pos;
  render();
});

document.getElementById('search').addEventListener('input', function(e) {
  currentSearch = e.target.value;
  render();
});

document.querySelectorAll('th[data-sort]').forEach(function(th) {
  th.addEventListener('click', function() {
    var col = this.dataset.sort;
    if (sortCol === col) { sortAsc = !sortAsc; }
    else { sortCol = col; sortAsc = col === 'name' || col === 'team' || col === 'displayPos' || col === 'status'; }
    document.querySelectorAll('th').forEach(function(t) { t.classList.remove('sorted-asc', 'sorted-desc'); });
    this.classList.add(sortAsc ? 'sorted-asc' : 'sorted-desc');
    render();
  });
});

render();

/* ===== Tab switching ===== */
document.querySelectorAll('.tab-btn').forEach(function(btn) {
  btn.addEventListener('click', function() {
    document.querySelectorAll('.tab-btn').forEach(function(b) { b.classList.remove('active'); });
    document.querySelectorAll('.tab-view').forEach(function(v) { v.classList.remove('active'); });
    this.classList.add('active');
    document.getElementById('tab-' + this.dataset.tab).classList.add('active');
  });
});

/* ===== Streaming tab rendering ===== */
var TIER_META = {
  must_start: {label: 'Must Start', cls: 'tier-must_start'},
  start:      {label: 'Start', cls: 'tier-start'},
  borderline: {label: 'Borderline', cls: 'tier-borderline'},
  avoid:      {label: 'Sit', cls: 'tier-avoid'},
};
var TIER_SEQ = ['must_start', 'start', 'borderline', 'avoid'];

function escHtml(v) {
  return String(v === null || v === undefined ? '' : v)
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
    .replace(/"/g, '&quot;');
}

function tierLabel(tier) {
  return TIER_META[tier] ? TIER_META[tier].label : (tier || 'unknown');
}

function renderDecisionItem(item) {
  var pts = Number(item.points || 0);
  var matchup = item.home_away === 'H' ? 'vs ' + (item.opponent || '?') : '@ ' + (item.opponent || '?');
  var conf = item.confidence || tierLabel(item.tier);
  var confCls = conf === 'Strong Start' ? 'conf-strong' : conf === 'Start' ? 'conf-start' : conf === 'Avoid' ? 'conf-avoid' : 'conf-borderline';
  var risks = (item.risks || []).slice(0, 2);
  var boosts = (item.boosts || []).slice(0, 2);
  var notes = [];
  if (risks.length) notes.push('<span class="decision-risk">Risk: ' + risks.map(escHtml).join('; ') + '</span>');
  if (boosts.length) notes.push('<span class="decision-boost">Boost: ' + boosts.map(escHtml).join('; ') + '</span>');
  if (!notes.length) notes.push('<span>Notes: none</span>');
  var labelHtml = item.watch_label ? '<span class="watch-label">' + escHtml(item.watch_label) + '</span> ' : '';
  var overlapHtml = item.also_listed ? '<span class="decision-overlap">Also listed above</span>' : '';
  return '<div class="decision-row">' +
    '<div class="decision-line1"><span class="decision-name">' + escHtml(item.name) + '</span><span class="decision-pts">' + pts.toFixed(1) + ' pts</span></div>' +
    '<div class="decision-meta">' + labelHtml + escHtml(item.team || '?') + ' &bull; ' + escHtml(item.status || 'UNKNOWN') + ' &bull; <span class="decision-confidence ' + confCls + '">' + escHtml(conf) + '</span> &bull; ' + escHtml(matchup) + ' (' + escHtml(item.home_away || '?') + ')</div>' +
    '<div class="decision-reasons">' +
      '<div><span class="decision-reason-label">Why:</span> ' + escHtml(item.main_reason || 'Projection is the main signal') + '</div>' +
      '<div><span class="decision-reason-label">Risk:</span> ' + escHtml(item.risk_reason || 'No major red flag in logged signals') + '</div>' +
    '</div>' +
    overlapHtml +
    '<div class="decision-notes">' + notes.join('<br>') + '</div>' +
    '</div>';
}

function renderDecisionSection(title, rows, emptyText) {
  var h = '<div class="decision-section"><div class="decision-section-title">' + escHtml(title) + '</div>';
  if (!rows || rows.length === 0) return h + '<div class="decision-empty">' + escHtml(emptyText || 'None') + '</div></div>';
  h += rows.map(renderDecisionItem).join('');
  return h + '</div>';
}

function renderRiskyRosterSection(rows) {
  var h = '<div class="decision-section"><div class="decision-section-title">Risky Rostered Starts</div>';
  if (!rows || rows.length === 0) return h + '<div class="decision-empty">No rostered starts flagged as risky.</div></div>';
  h += '<div class="decision-compact-list">';
  h += rows.map(function(item) {
    var pts = Number(item.points || 0);
    var matchup = item.home_away === 'H' ? 'vs ' + (item.opponent || '?') : '@ ' + (item.opponent || '?');
    var conf = item.confidence || tierLabel(item.tier);
    var confCls = conf === 'Strong Start' ? 'conf-strong' : conf === 'Start' ? 'conf-start' : conf === 'Avoid' ? 'conf-avoid' : 'conf-borderline';
    var risk = item.risk_reason || (item.risks && item.risks.length ? item.risks[0] : 'Risk flag in logged signals');
    return '<div class="decision-compact-row">' +
      '<div class="decision-compact-main"><div class="decision-name">' + escHtml(item.name) + '</div><div class="decision-compact-meta">' + pts.toFixed(1) + ' pts &bull; ' + escHtml(matchup) + '</div></div>' +
      '<div class="decision-confidence ' + confCls + '">' + escHtml(conf) + '</div>' +
      '<div class="decision-compact-risk" title="' + escHtml(risk) + '">Risk: ' + escHtml(risk) + ' <span class="decision-overlap">Also listed above</span></div>' +
      '</div>';
  }).join('');
  return h + '</div></div>';
}

function renderProblemSection(problems) {
  var h = '<div class="decision-section"><div class="decision-section-title">TBD / Problem Games</div>';
  if (!problems || problems.length === 0) return h + '<div class="decision-empty">No problems flagged.</div></div>';
  h += problems.map(function(p) { return '<div class="decision-row"><div class="decision-notes">' + escHtml(p) + '</div></div>'; }).join('');
  return h + '</div>';
}

function actionKindClass(kind) {
  return String(kind || 'WATCH').toLowerCase().replace(/\s+/g, '-');
}

function renderActionRows(items, limit) {
  if (!items || !items.length) return '<div class="decision-empty">No matchup actions available.</div>';
  var h = '<div class="action-list">';
  items.slice(0, limit || 10).forEach(function(item) {
    var kind = item.kind || 'WATCH';
    var metaParts = [];
    if (item.meta) {
      if (item.meta.source) metaParts.push(item.meta.source);
      if (item.meta.context) metaParts.push(item.meta.context);
      if (item.meta.game_date) metaParts.push(item.meta.game_date);
      if (item.meta.opponent) metaParts.push('vs ' + item.meta.opponent);
      if (item.meta.snapshot_date) metaParts.push('snapshot ' + item.meta.snapshot_date);
      if (item.meta.note) metaParts.push(item.meta.note);
    }
    if (!metaParts.length && item.date_label) metaParts.push(item.date_label);
    if (!metaParts.length && item.source) metaParts.push(item.source);
    h += '<div class="action-row">';
    h += '<span class="action-kind ' + actionKindClass(kind) + '">' + escHtml(kind) + '</span>';
    h += '<div class="action-text">' + escHtml(item.text || '') + '</div>';
    h += '<div class="action-meta">' + metaParts.map(escHtml).join(' &bull; ') + '</div>';
    h += '</div>';
  });
  h += '</div>';
  return h;
}

function renderHitterActionSection(title, items, emptyText, limit) {
  var h = '<div class="decision-section"><div class="decision-section-title">' + escHtml(title) + '</div>';
  if (!items || !items.length) {
    h += '<div class="decision-empty">' + escHtml(emptyText || 'No hitter actions available.') + '</div></div>';
    return h;
  }
  h += renderActionRows(items, limit || 6);
  h += '</div>';
  return h;
}

function renderMatchupReport() {
  var container = document.getElementById('matchupContent');
  if (!container) return;
  var s = MATCHUP_SNAPSHOT || {};
  var a = MATCHUP_ACTIONS || {};
  var h = '<div class="day-card decision-card">';
  h += '<div class="day-header"><span class="day-date">Matchup Snapshot</span><span class="day-count">' + escHtml(s.available ? ('Period ' + (s.scoring_period || '?')) : 'Unavailable') + '</span></div>';
  if (!s.available) {
    h += '<div class="decision-warning">' + escHtml(s.error || 'ESPN matchup data unavailable. The rest of the report is still usable.') + '</div>';
  } else {
    var mine = Number(s.my_score);
    var opp = Number(s.opponent_score);
    var margin = Number(s.margin);
    var hasScore = isFinite(mine) && isFinite(opp);
    var marginCls = margin >= 0 ? 'good' : 'bad';
    h += '<div class="matchup-grid">';
    h += '<div class="decision-section"><div class="decision-section-title">Current Matchup</div><div class="decision-row">';
    h += '<div class="decision-line1"><span class="decision-name">' + escHtml(s.my_team || 'My team') + '</span><span class="decision-meta">vs ' + escHtml(s.opponent || 'Opponent') + '</span></div>';
    h += '<div class="matchup-score">' + (hasScore ? (mine.toFixed(1) + ' - ' + opp.toFixed(1)) : 'Score unavailable') + '</div>';
    if (hasScore) h += '<div class="matchup-margin ' + marginCls + '">Margin ' + (margin >= 0 ? '+' : '') + margin.toFixed(1) + '</div>';
    h += '<div class="matchup-small">Active: ' + (s.my_active_count || 0) + ' mine, ' + (s.opponent_active_count || 0) + ' opponent &bull; Injury notes: ' + (s.injury_note_count || 0) + '</div>';
    h += '</div></div>';
    h += '<div class="decision-section"><div class="decision-section-title">Matchup Actions</div>';
    h += renderActionRows((a.items || []), 10);
    if (a.notes && a.notes.length) h += '<div class="decision-warning">' + a.notes.map(escHtml).join(' ') + '</div>';
    h += '</div></div>';
  }
  h += '</div>';
  container.innerHTML = h;
}

function renderMatchupEdge() {
  var container = document.getElementById('matchupEdgeContent');
  if (!container || !MATCHUP_EDGE) return;
  var e = MATCHUP_EDGE || {};
  var h = '<div class="day-card decision-card">';
  h += '<div class="day-header"><span class="day-date">Matchup Edge</span><span class="day-count">' + escHtml(e.label || 'High uncertainty') + '</span></div>';
  if (!e.available) {
    h += '<div class="decision-warning">' + escHtml(e.error || 'Matchup edge unavailable.') + '</div>';
  } else {
    var score = e.current_score || {};
    var rem = e.remaining || {};
    var fin = e.projected_final || {};
    var cov = e.coverage || {};
    h += '<div class="decision-summary">';
    h += '<span class="decision-pill">Current <b>' + escHtml(score.mine) + ' - ' + escHtml(score.opponent) + '</b></span>';
    h += '<span class="decision-pill">Margin <b>' + escHtml(score.margin) + '</b></span>';
    h += '<span class="decision-pill">Remaining <b>' + Number(rem.mine || 0).toFixed(1) + ' - ' + Number(rem.opponent || 0).toFixed(1) + '</b></span>';
    h += '<span class="decision-pill">Projected final <b>' + escHtml(fin.mine) + ' - ' + escHtml(fin.opponent) + '</b></span>';
    h += '<span class="decision-pill">Edge <b>' + escHtml(fin.edge) + '</b></span>';
    h += '<span class="decision-pill">Confidence <b>' + escHtml(e.confidence || 'low') + '</b></span>';
    h += '</div>';
    h += '<div class="matchup-small">Coverage: ' + (cov.projected_players || 0) + '/' + (cov.total_players || 0) + ' players projected (' + (cov.coverage_pct || 0) + '%). Rough projection only, not a win probability.</div>';
  }
  if (e.recommendations && e.recommendations.length) {
    h += '<div class="decision-section"><div class="decision-section-title">Posture Recommendations</div>';
    h += '<div class="action-list">';
    e.recommendations.forEach(function(rec) {
      h += '<div class="action-row"><span class="action-kind watch">WATCH</span><div class="action-text">' + escHtml(rec) + '</div></div>';
    });
    h += '</div></div>';
  }
  if (e.notes && e.notes.length) h += '<div class="decision-warning">' + e.notes.map(escHtml).join(' ') + '</div>';
  h += '</div>';
  container.innerHTML = h;
}

function renderHitterDecisions() {
  var container = document.getElementById('hitterDecisionContent');
  if (!container || !HITTER_DECISIONS) return;
  var h = '<div class="day-card decision-card">';
  var items = HITTER_DECISIONS.items || [];
  var lineupAlerts = items.filter(function(item) {
    return ['INJURY CHECK', 'NO GAME', 'BENCH'].indexOf(item.kind || '') !== -1;
  });
  var hitterAdds = items.filter(function(item) {
    return ['ADD', 'START', 'WATCH'].indexOf(item.kind || '') !== -1;
  });
  var contextCounts = { high: 0, medium: 0, low: 0, unlabeled: 0 };
  items.forEach(function(item) {
    var label = item.context_confidence || '';
    if (label === 'High context') contextCounts.high += 1;
    else if (label === 'Medium context') contextCounts.medium += 1;
    else if (label === 'Low context') contextCounts.low += 1;
    else contextCounts.unlabeled += 1;
  });
  var data = HITTER_DECISIONS.data_available || {};
  var context = HITTER_DECISIONS.daily_context || {};
  var coverage = context.coverage || {};
  h += '<div class="day-header"><span class="day-date">Hitter Decisions</span><span class="day-count">' + items.length + ' action' + (items.length === 1 ? '' : 's') + '</span></div>';
  h += '<div class="decision-summary">';
  h += '<span class="decision-pill">Active hitters <b>' + (HITTER_DECISIONS.active_hitter_count || 0) + '</b></span>';
  h += '<span class="decision-pill">Bench hitters <b>' + (HITTER_DECISIONS.bench_hitter_count || 0) + '</b></span>';
  h += '<span class="decision-pill">FA candidates <b>' + (HITTER_DECISIONS.fa_hitter_candidates || 0) + '</b></span>';
  h += '<span class="decision-pill">Team games <b>' + (data.team_game_schedule ? 'yes' : 'no') + '</b></span>';
  if (coverage.total_rows !== undefined) {
    h += '<span class="decision-pill">Context rows <b>' + (coverage.total_rows || 0) + '</b></span>';
    h += '<span class="decision-pill">Opp SP quality <b>' + (coverage.with_opposing_pitcher_quality || 0) + '</b></span>';
    h += '<span class="decision-pill">Park/venue <b>' + (coverage.with_park_or_venue || 0) + '</b></span>';
    h += '<span class="decision-pill">Pitcher hand <b>' + (coverage.with_opposing_pitcher_hand || 0) + '</b></span>';
    h += '<span class="decision-pill">Hitter bats <b>' + (coverage.with_hitter_bats || 0) + '</b></span>';
    h += '<span class="decision-pill">Platoon context <b>' + (coverage.with_hitter_platoon_context || 0) + '</b></span>';
    h += '<span class="decision-pill">Lineup spot <b>' + (coverage.with_lineup_spot || 0) + '</b></span>';
    h += '<span class="decision-pill">Posted lineups <b>' + (coverage.teams_with_posted_lineups || 0) + '</b></span>';
  }
  h += '</div>';
  if (context.notes && context.notes.length) {
    h += '<div class="matchup-small">' + context.notes.map(escHtml).join(' ') + '</div>';
  }
  h += '<div class="matchup-small">Hitter context confidence: ';
  h += '<b>' + contextCounts.high + '</b> high, ';
  h += '<b>' + contextCounts.medium + '</b> medium, ';
  h += '<b>' + contextCounts.low + '</b> low';
  if (contextCounts.unlabeled) h += ', <b>' + contextCounts.unlabeled + '</b> unlabeled';
  if (coverage.total_rows !== undefined && !(coverage.with_lineup_spot || 0)) {
    h += '. Lineups not posted yet, so hitter advice is context-limited.';
  } else if (coverage.total_rows !== undefined && (coverage.with_lineup_spot || 0) < (coverage.total_rows || 0)) {
    h += '. Some lineups are still missing.';
  }
  h += '</div>';
  h += '<div class="matchup-grid">';
  h += renderHitterActionSection(
    'Hitter Lineup Alerts',
    lineupAlerts,
    'No active hitter injury, no-game, or posted-lineup alerts.',
    6
  );
  h += renderHitterActionSection(
    'Hitter Adds',
    hitterAdds,
    'No FA/bench hitter add notes available from current context.',
    6
  );
  h += '</div>';
  if (HITTER_DECISIONS.notes && HITTER_DECISIONS.notes.length) {
    h += '<div class="decision-warning">' + HITTER_DECISIONS.notes.map(escHtml).join(' ') + '</div>';
  }
  h += '</div>';
  container.innerHTML = h;
}

function renderDailyDecisions() {
  var container = document.getElementById('decisionContent');
  if (!container || !DAILY_DECISIONS) return;
  var d = DAILY_DECISIONS;
  var sections = d.sections || {};
  var h = '<div class="day-card decision-card">';
  h += '<div class="day-header"><span class="day-date">Today&rsquo;s Pitching Decisions</span><span class="day-count">' + escHtml(d.date || '') + '</span></div>';
  if (d.warning) h += '<div class="decision-warning">' + escHtml(d.warning) + '</div>';
  h += '<div class="decision-summary">';
  h += '<span class="decision-pill">Rows scanned <b>' + (d.rows_scanned || 0) + '</b></span>';
  h += '<span class="decision-pill">Actionable <b>' + (d.actionable_count || 0) + '</b></span>';
  h += '<span class="decision-pill">MY ROSTER <b>' + (d.roster_count || 0) + '</b></span>';
  h += '<span class="decision-pill">FA <b>' + (d.fa_count || 0) + '</b></span>';
  h += '<span class="decision-pill">WAIVER <b>' + (d.waiver_count || 0) + '</b></span>';
  h += '<span class="decision-pill">Hidden OTHER <b>' + (d.hidden_other_count || 0) + '</b></span>';
  h += '<span class="decision-pill">Hidden unknown <b>' + (d.hidden_unknown_count || 0) + '</b></span>';
  h += '</div>';
  h += '<div class="decision-grid">';
  h += renderDecisionSection('Best FA / Waiver Streamers', sections.best_available, 'No available streamers above the filter.');
  h += renderDecisionSection('My Rostered Starters', sections.my_roster, 'No rostered starters found today.');
  h += renderRiskyRosterSection(sections.risky_roster);
  h += renderDecisionSection('Avoid / Trap FA Starts', sections.avoid_traps, 'No FA traps flagged.');
  h += renderProblemSection(d.problems);
  h += '</div></div>';
  container.innerHTML = h;
}

function renderAddDropPriority() {
  var container = document.getElementById('addDropContent');
  if (!container || !ADD_DROP_PRIORITY) return;
  var items = ADD_DROP_PRIORITY.items || [];
  var h = '<div class="day-card decision-card">';
  h += '<div class="day-header"><span class="day-date">Add / Drop Priority</span><span class="day-count">' + items.length + ' action' + (items.length === 1 ? '' : 's') + '</span></div>';
  if (!items.length) {
    h += '<div class="decision-empty">No priority add/drop actions from the current prediction set.</div>';
  } else {
    h += '<div class="action-list">';
    items.forEach(function(item) {
      var kind = actionKindClass(item.kind || 'WATCH');
      var meta = (item.date_label || '') + ' &bull; ' + (item.status || '') + ' &bull; ' + (Number(item.points || 0)).toFixed(1) + ' pts';
      h += '<div class="action-row">';
      h += '<span class="action-kind ' + kind + '">' + escHtml(item.kind || 'WATCH') + '</span>';
      h += '<div class="action-text">' + escHtml(item.text || '') + '</div>';
      h += '<div class="action-meta">' + meta.split(' &bull; ').map(escHtml).join(' &bull; ') + '</div>';
      h += '</div>';
    });
    h += '</div>';
  }
  h += '</div>';
  container.innerHTML = h;
}

function renderWatchlist() {
  var container = document.getElementById('watchlistContent');
  if (!container || !NEXT_WATCHLIST) return;
  var w = NEXT_WATCHLIST;
  var h = '<div class="day-card decision-card">';
  h += '<div class="day-header"><span class="day-date">Next 3 Days Watchlist</span><span class="day-count">' + escHtml(w.date_range || '') + '</span></div>';
  h += '<div class="decision-summary">';
  h += '<span class="decision-pill">Rows scanned <b>' + (w.rows_scanned || 0) + '</b></span>';
  h += '<span class="decision-pill">Actionable <b>' + (w.actionable_count || 0) + '</b></span>';
  h += '<span class="decision-pill">Hidden OTHER <b>' + (w.hidden_other_count || 0) + '</b></span>';
  h += '<span class="decision-pill">Hidden unknown <b>' + (w.hidden_unknown_count || 0) + '</b></span>';
  h += '</div>';
  if (w.problems && w.problems.length) {
    h += '<div class="decision-warning">' + w.problems.map(escHtml).join(' ') + '</div>';
  }
  if (!w.days || w.days.length === 0) {
    h += '<div class="decision-empty">No actionable upcoming starts found.</div>';
  } else {
    w.days.forEach(function(day) {
      h += '<div class="watch-day">';
      h += '<div class="watch-date">' + escHtml(day.label || day.date || '') + '</div>';
      h += '<div class="decision-grid watch-grid">';
      h += (day.items || []).map(renderDecisionItem).join('');
      h += '</div></div>';
    });
  }
  h += '</div>';
  container.innerHTML = h;
}

function renderStreaming() {
  var container = document.getElementById('streamContent');
  if (!STREAMING || STREAMING.length === 0) {
    container.innerHTML = '<div class="stream-note" style="padding:40px;text-align:center;color:#555">No streaming data available. Run the tracker to fetch probable pitchers.</div>';
    return;
  }
  // Group by date
  var days = {};
  var dayOrder = [];
  STREAMING.forEach(function(s) {
    if (!days[s.date]) { days[s.date] = {date: s.date, day: s.day, entries: []}; dayOrder.push(s.date); }
    days[s.date].entries.push(s);
  });
  var html = '';
  dayOrder.forEach(function(d) {
    var day = days[d];
    var dateObj = new Date(day.date + 'T12:00:00');
    var dateLabel = dateObj.toLocaleDateString('en-US', {weekday: 'long', month: 'short', day: 'numeric'});
    var realEntries = day.entries.filter(function(e) { return !e.tbd; });
    var tbdCount = day.entries.length - realEntries.length;

    html += '<div class="day-card">';
    html += '<div class="day-header"><span class="day-date">' + dateLabel + '</span>';
    html += '<span class="day-count">' + realEntries.length + ' option' + (realEntries.length !== 1 ? 's' : '');
    if (tbdCount > 0) html += ' + ' + tbdCount + ' TBD';
    html += '</span></div>';

    // Group entries by tier within the day
    var byTier = {};
    var tbds = [];
    day.entries.forEach(function(s) {
      if (s.tbd) { tbds.push(s); return; }
      var t = s.tier || 'borderline';
      if (!byTier[t]) byTier[t] = [];
      byTier[t].push(s);
    });

    TIER_SEQ.forEach(function(tier) {
      var entries = byTier[tier];
      if (!entries || entries.length === 0) return;
      var meta = TIER_META[tier];
      html += '<div class="tier-header ' + meta.cls + '">' + meta.label + '</div>';
      entries.forEach(function(s) { html += renderPitcherEntry(s, realEntries); });
    });

    // TBDs at the bottom
    tbds.forEach(function(s) {
      var note = s.probable_note ? ' — ' + s.probable_note : '';
      var pitcher = s.probable_conflict_pitcher ? ' (' + s.probable_conflict_pitcher + ')' : '';
      html += '<div class="stream-tbd">' + s.team + ' vs ' + s.opponent + ' (' + s.home_away + ') — probable pitcher TBD/problem' + pitcher + escHtml(note) + '</div>';
    });

    html += '</div>';
  });
  container.innerHTML = html;
}

function shortReason(text, maxLen) {
  text = String(text || '');
  maxLen = maxLen || 72;
  return text.length > maxLen ? text.slice(0, maxLen - 1).trim() + '…' : text;
}

function pushUnique(list, text) {
  if (text && list.indexOf(text) === -1) list.push(text);
}

function pitchFitPhrase(s, kind) {
  var pa = s.pitch_analysis || {};
  var pitches = pa.pitches || [];
  var pitch = null;
  for (var i = 0; i < pitches.length; i++) {
    if (kind === 'good' && (pitches[i].matchup === 'strong' || pitches[i].matchup === 'favorable')) {
      pitch = pitches[i]; break;
    }
    if (kind === 'bad' && (pitches[i].matchup === 'poor' || pitches[i].matchup === 'unfavorable')) {
      pitch = pitches[i]; break;
    }
  }
  if (!pitch) return '';
  var name = String(pitch.name || 'pitch').toLowerCase();
  var grade = pitch.grade ? String(pitch.grade) + ' ' : '';
  if (kind === 'good') return grade + name + ' lines up well';
  return name + ' is a matchup concern';
}

function streamingRiskGuardSignals(s) {
  var signals = [];
  var score = 0;
  var recentEra = Number(s.recent_era);
  var oppRank = Number(s.opp_rank || 15);
  var parkFactor = Number(s.park_factor || 0);
  var k9 = Number(s.k9 || s.proj_k9 || 0);
  var workload = Number(s.workload_risk_score || 0);
  var pitchScore = s.pitch_matchup_score === null || s.pitch_matchup_score === undefined
    ? null : Number(s.pitch_matchup_score);

  if (s.trend === 'cold') {
    score += 2;
    signals.push('COLD tag');
  }
  if (isFinite(recentEra) && recentEra >= 5.14) {
    score += 1;
    signals.push('recent ERA >= 5.14');
  }
  if (isFinite(oppRank) && oppRank <= 10) {
    score += 1;
    signals.push('top-10 opponent offense');
  }
  if (parkFactor && parkFactor >= 1.05) {
    score += 1;
    signals.push('hitter-friendly park');
  }
  if (s.platoon === 'risk') {
    score += 1;
    signals.push('platoon risk');
  }
  if (k9 && k9 < 7.5) {
    score += 1;
    signals.push('low K/9');
  }
  if (workload && workload >= 0.4) {
    score += 1;
    signals.push('workload risk');
  }
  if (pitchScore !== null && isFinite(pitchScore) && pitchScore <= -0.05) {
    score += 1;
    signals.push('negative pitch matchup');
  }
  return {score: score, signals: signals};
}

function streamingRiskGuardWarning(s) {
  var tier = s.tier || '';
  if (s.risk_guard_applied) {
    var original = tierLabel(s.risk_guard_original_tier || s.model_tier || '');
    var display = tierLabel(s.risk_guard_display_tier || s.tier || '');
    var reasons = s.risk_guard_reasons || s.shadow_risk_guard_reasons || [];
    var reasonText = reasons.length ? reasons.slice(0, 3).join(', ') : 'multiple risk flags';
    return '<div class="stream-caution"><b>Risk guard:</b> downgraded from ' +
      escHtml(original) + ' to ' + escHtml(display) + ' because ' + escHtml(reasonText) +
      '. Points are unchanged; recommendation is more conservative.</div>';
  }
  if (tier !== 'must_start' && tier !== 'start' && tier !== 'borderline') return '';
  var risk = streamingRiskGuardSignals(s);
  if (!(s.trend === 'cold' || risk.signals.indexOf('recent ERA >= 5.14') !== -1 || risk.score >= 2)) {
    return '';
  }
  var lead = tier === 'borderline'
    ? 'Borderline only'
    : 'Start with caution';
  var signals = risk.signals.slice(0, 3).join(', ');
  var note = 'Backtest caution: ' + signals + ' has been linked to more bust risk.';
  return '<div class="stream-caution"><b>' + escHtml(lead) + ':</b> ' + escHtml(note) + '</div>';
}

function streamingExplanation(s) {
  if (s.risk_guard_applied) {
    var original = tierLabel(s.risk_guard_original_tier || s.model_tier || '');
    var display = tierLabel(s.risk_guard_display_tier || s.tier || '');
    var guardReasons = (s.risk_guard_reasons || []).slice(0, 3).map(function(x) { return shortReason(x, 58); }).join('; ');
    return '<div class="stream-explain"><b class="why-borderline">Why downgraded:</b> ' +
      escHtml('Model tier was ' + original + ', but risk guard shows ' + display + ' because ' + (guardReasons || 'multiple risk flags')) +
      '. <b>Upside:</b> ' + escHtml('projection remains ' + Number(s.pts || 0).toFixed(1) + ' points.') + '</div>';
  }
  var reasons = [];
  var risks = [];
  var pts = Number(s.pts || 0);
  var oppRank = Number(s.opp_rank || 15);
  var parkFactor = Number(s.park_factor || 0);

  if (pts >= 12) pushUnique(reasons, 'strong point projection');
  else if (pts >= 8) pushUnique(reasons, 'playable point projection');
  else pushUnique(risks, 'light point projection');

  if (oppRank >= 21) pushUnique(reasons, 'soft opponent offense');
  else if (oppRank <= 10) pushUnique(risks, 'tough opponent offense');

  if (parkFactor && parkFactor <= 0.96) pushUnique(reasons, 'pitcher-friendly park');
  else if (parkFactor && parkFactor >= 1.05) pushUnique(risks, 'hitter-friendly park');

  if (s.platoon === 'edge') pushUnique(reasons, 'platoon edge');
  else if (s.platoon === 'risk') pushUnique(risks, 'platoon risk');

  if (s.trend === 'hot') pushUnique(reasons, 'recent form is hot');
  else if (s.trend === 'cold') pushUnique(risks, 'cold tag: L14D ERA is 1.5+ runs worse than projection');

  var goodPitch = pitchFitPhrase(s, 'good');
  var badPitch = pitchFitPhrase(s, 'bad');
  if (goodPitch) pushUnique(reasons, goodPitch);
  if (badPitch) pushUnique(risks, badPitch);

  if (s.opp_il && s.opp_il.length) pushUnique(reasons, 'opponent missing bat(s)');
  if (s.opp_il_returns && s.opp_il_returns.length) pushUnique(risks, 'opponent getting bat(s) back');
  if (s.probable_warning) pushUnique(risks, shortReason(s.probable_warning, 68));

  if (!reasons.length) pushUnique(reasons, 'projection is the main positive signal');
  if (!risks.length) pushUnique(risks, 'normal streamer volatility');

  var tier = s.tier || 'borderline';
  var label = 'Why borderline';
  var cls = 'why-borderline';
  var lead = 'Playable, not safe';
  if (tier === 'must_start' || tier === 'start') {
    label = 'Why start';
    cls = 'why-start';
    lead = 'Start';
  } else if (tier === 'avoid') {
    label = 'Why sit';
    cls = 'why-sit';
    lead = 'Sit';
  }

  var mainBits = tier === 'avoid' ? risks.slice(0, 2) : reasons.slice(0, 2);
  var riskBits = tier === 'avoid' ? reasons.slice(0, 1) : risks.slice(0, 2);
  var counterLabel = tier === 'avoid' ? 'Counterpoint' : 'Risk';
  return '<div class="stream-explain"><b class="' + cls + '">' + label + ':</b> ' +
    escHtml(lead + ' because ' + mainBits.map(function(x) { return shortReason(x, 58); }).join('; ')) +
    '. <b>' + counterLabel + ':</b> ' +
    escHtml(riskBits.map(function(x) { return shortReason(x, 58); }).join('; ')) +
    '.</div>';
}

function renderPitcherEntry(s, allReal) {
  var topPts = allReal.length > 0 ? Math.max.apply(null, allReal.filter(function(e){return e.status==='FA'}).map(function(e){return e.pts||0})) : 0;
  var isTop = s.pts === topPts && s.status === 'FA' && topPts > 0;
  var isMine = s.status === 'MY ROSTER';
  var cls = 'stream-entry';
  if (isMine) cls += ' stream-mine';
  else if (isTop) cls += ' stream-top';

  var ptsCls = s.pts >= 12 ? 'pts-good' : s.pts >= 8 ? 'pts-ok' : 'pts-bad';

  var tagHtml = '';
  if (s.tag === 'ACE') tagHtml = '<span class="chip chip-ace">ACE</span>';
  else if (s.tag === 'SAFE') tagHtml = '<span class="chip chip-safe">SAFE</span>';
  else if (s.tag === 'UPSIDE') tagHtml = '<span class="chip chip-upside">UPSIDE</span>';
  if (isMine) tagHtml += '<span class="chip chip-mine">ROSTER</span>';
  if (s.emerging) tagHtml += '<span class="chip chip-emerging" title="Based on L14D stats through $HOLD_ASOF">HOLD</span>';
  if (s.risk_guard_applied) tagHtml += '<span class="chip chip-upside" title="Visible recommendation downgraded by the risk guard; points unchanged.">RISK GUARD</span>';

  var matchup = s.home_away === 'H' ? 'vs ' + s.opponent : '@' + s.opponent;

  var h = '<div class="' + cls + '">';
  // Row 1
  h += '<div class="stream-row1">';
  if (isTop) h += '<span class="stream-name"><span class="star">\u2605</span>' + s.name + '</span>';
  else h += '<span class="stream-name">' + s.name + '</span>';
  h += '<span class="stream-team">' + s.team + '</span>';
  h += '<span class="stream-matchup">' + matchup + ' (' + s.home_away + ')</span>';
  var ptsHtml = '<span class="stream-pts ' + ptsCls + '">' + s.pts.toFixed(1) + ' pts</span>';
  if (s.adj_total && Math.abs(s.adj_total) >= 0.3 && s.adjustments && s.adjustments.length) {
    var adjCls = s.adj_total > 0 ? 'adj-up' : 'adj-down';
    var adjText = (s.adj_total >= 0 ? '+' : '') + s.adj_total.toFixed(1);
    var lines = s.adjustments.map(function(a) {
      var d = (a.delta >= 0 ? '+' : '') + a.delta.toFixed(2);
      return '• ' + (a.label || '(no label)') + '  [' + d + ']';
    });
    var tip = 'Auto-adjustments based on accumulated outcomes:\n' + lines.join('\n')
            + '\n\nBase prediction: ' + (s.pts_pre_adj || s.pts).toFixed(1) + ' pts\nAdjusted: ' + s.pts.toFixed(1) + ' pts';
    ptsHtml += '<span class="adj-chip ' + adjCls + '" title="' + tip.replace(/"/g, '&quot;') + '">' + adjText + '</span>';
  }
  h += ptsHtml;
  h += '<span class="stream-stat">ERA <b>' + s.era.toFixed(2) + '</b></span>';
  h += '<span class="stream-stat">K/9 <b>' + s.k9.toFixed(1) + '</b></span>';
  h += tagHtml;
  h += '</div>';

  // Row 2: matchup context
  h += '<div class="stream-row2">';
  var oppRank = s.opp_rank || 15;
  var oppCls = oppRank <= 10 ? 'opp-hard' : oppRank >= 21 ? 'opp-easy' : 'opp-mid';
  h += '<span>vs <span class="' + oppCls + '">' + ordinal(oppRank) + ' offense (' + s.opp_ops + ' OPS)</span></span>';
  // Park factor
  if (s.park_factor && s.park_factor >= 1.05) {
    var pf = s.park_factor.toFixed(2);
    h += '<span>\u2022 <span class="park-penalty">\u26A0 ' + s.park + ' park (' + pf + ')</span></span>';
  } else if (s.park_factor && s.park_factor <= 0.96) {
    var pf = s.park_factor.toFixed(2);
    h += '<span>\u2022 <span class="park-boost">\u2714 ' + s.park + ' park (' + pf + ')</span></span>';
  }
  if (s.platoon === 'edge') h += '<span>\u2022 <span class="platoon-edge">\u2714 platoon edge</span></span>';
  else if (s.platoon === 'risk') h += '<span>\u2022 <span class="platoon-risk">\u26A0 platoon risk</span></span>';
  if (s.opp_hand) h += '<span>\u2022 opp lineup: ' + s.opp_hand + '</span>';
  if (s.vs_l_ops && s.vs_r_ops) {
    var splitsLabel = s.splits_window_years ? ('L' + s.splits_window_years) : 'recent';
    h += '<span title="IP-weighted average over the last ' + (s.splits_window_years || 3) + ' seasons. Career averages mask aging-vet decline.">\u2022 ' + splitsLabel + ' vs L: ' + s.vs_l_ops + ' / vs R: ' + s.vs_r_ops + '</span>';
  }
  if (s.trend === 'hot') h += '<span>\u2022 <span class="trend-hot">\u25B2 HOT</span> (' + (s.recent_era !== null ? s.recent_era.toFixed(2) + ' ERA L14D' : '') + ')</span>';
  else if (s.trend === 'cold') h += '<span>\u2022 <span class="trend-cold">\u25BC COLD</span> (' + (s.recent_era !== null ? s.recent_era.toFixed(2) + ' ERA L14D' : '') + ')</span>';
  // Opponent IL: notable hitters missing from opponent lineup
  if (s.opp_il && s.opp_il.length > 0) {
    var ilNames = s.opp_il.map(function(il) {
      return il.name + ' (' + il.il_type + ')';
    }).join(', ');
    h += '<span>\u2022 <span class="opp-il-boost">\u2714 ' + s.opponent + ' missing: ' + ilNames + '</span></span>';
  }
  // Recently activated stars: opponent stronger than recent stats suggest
  if (s.opp_il_returns && s.opp_il_returns.length > 0) {
    var retNames = s.opp_il_returns.map(function(r) { return r.name; }).join(', ');
    h += '<span>\u2022 <span class="opp-il-warn">\u26A0 ' + s.opponent + ' just activated: ' + retNames + '</span></span>';
  }
  if (s.probable_warning) {
    h += '<span>\u2022 <span class="opp-il-warn">\u26A0 ' + escHtml(s.probable_warning) + '</span></span>';
  }
  h += '</div>';

  h += streamingRiskGuardWarning(s);

  // Row 3: pitch arsenal matchup
  var pa = s.pitch_analysis;
  if (pa && pa.pitches && pa.pitches.length > 0) {
    h += '<div class="stream-row3"><div class="pitch-bar">';
    pa.pitches.forEach(function(p) {
      var pillCls = 'pitch-pill';
      if (p.grade === 'elite') pillCls += ' pitch-elite';
      else if (p.grade === 'plus') pillCls += ' pitch-plus';
      else if (p.grade === 'weak') pillCls += ' pitch-weak';

      var whiffStr = p.whiff !== null ? p.whiff.toFixed(0) + '% whiff' : '';
      var matchCls = p.matchup ? 'pitch-matchup-' + p.matchup : '';
      var matchLabel = '';
      if (p.matchup === 'strong') matchLabel = '\u2191\u2191';
      else if (p.matchup === 'favorable') matchLabel = '\u2191';
      else if (p.matchup === 'poor') matchLabel = '\u2193\u2193';
      else if (p.matchup === 'unfavorable') matchLabel = '\u2193';

      h += '<span class="' + pillCls + '">';
      h += '<span class="pitch-name">' + p.name + '</span>';
      h += '<span class="pitch-detail">' + p.usage.toFixed(0) + '%</span>';
      if (whiffStr) h += '<span class="pitch-detail">' + whiffStr + '</span>';
      if (matchLabel) h += '<span class="' + matchCls + '">' + matchLabel + '</span>';
      h += '</span>';
    });
    if (pa.summary) h += '<span class="pitch-summary">' + pa.summary + '</span>';
    h += '</div></div>';
  } else if (s.fb_velo) {
    h += '<div class="stream-row3"><div class="pitch-bar">';
    h += '<span class="pitch-pill"><span class="pitch-name">FB</span><span class="pitch-detail">' + s.fb_velo.toFixed(1) + 'mph</span></span>';
    if (s.pitch_count) h += '<span style="color:#666;font-size:10px">' + s.pitch_count + ' pitch types</span>';
    h += '</div></div>';
  }

  h += streamingExplanation(s);

  h += '</div>';
  return h;
}

function ordinal(n) {
  var s = ['th','st','nd','rd'], v = n % 100;
  return n + (s[(v-20)%10] || s[v] || s[0]);
}

renderMatchupReport();
renderMatchupEdge();
renderHitterDecisions();
renderDailyDecisions();
renderAddDropPriority();
renderWatchlist();
renderStreaming();

/* ===== Accuracy tab rendering ===== */
function renderAccuracy() {
  var c = document.getElementById('accuracyContent');
  if (CALIBRATION && CALIBRATION.note) {
    c.innerHTML = '<div class="stream-note" style="padding:40px;text-align:center;color:#555">' + CALIBRATION.note + '</div>';
    return;
  }
  if (!CALIBRATION || !CALIBRATION.n) {
    c.innerHTML = '<div class="stream-note" style="padding:40px;text-align:center;color:#555">No outcomes joined yet. Predictions logged today; accuracy stats will populate after tomorrow’s outcomes are processed.</div>';
    return;
  }
  var cal = CALIBRATION;
  var biasDir = cal.bias > 0 ? 'underpredicting' : (cal.bias < 0 ? 'overpredicting' : 'on the nose');
  var biasCls = Math.abs(cal.bias) > 1 ? 'opp-hard' : 'opp-easy';

  var h = '';
  // Top stats row
  h += '<div class="day-card accuracy-card">';
  h += '<div class="day-header"><span>Last ' + cal.window_days + ' days &mdash; ' + cal.n + ' starts</span></div>';
  h += '<div class="accuracy-stats">';
  h += '<div class="accuracy-stat"><div style="color:#777;font-size:11px;text-transform:uppercase;letter-spacing:0.5px">MAE</div><div style="font-size:20px;font-weight:700">' + cal.mae.toFixed(2) + ' <span style="font-size:12px;color:#777">pts/start</span></div></div>';
  h += '<div class="accuracy-stat"><div style="color:#777;font-size:11px;text-transform:uppercase;letter-spacing:0.5px">RMSE</div><div style="font-size:20px;font-weight:700">' + cal.rmse.toFixed(2) + '</div></div>';
  h += '<div class="accuracy-stat"><div style="color:#777;font-size:11px;text-transform:uppercase;letter-spacing:0.5px">Bias</div><div style="font-size:20px;font-weight:700"><span class="' + biasCls + '">' + (cal.bias >= 0 ? '+' : '') + cal.bias.toFixed(2) + '</span> <span style="font-size:12px;color:#777">' + biasDir + '</span></div></div>';
  h += '</div></div>';

  // Per-tier table
  h += '<div class="day-card accuracy-card">';
  h += '<div class="day-header"><span>Per-tier accuracy</span><span style="color:#777;font-size:11px">predicted vs actual mean pts</span></div>';
  h += '<div class="accuracy-table-wrap">';
  h += '<table class="accuracy-table">';
  h += '<tr style="color:#777;font-size:11px;text-transform:uppercase;letter-spacing:0.5px"><td style="padding:4px 16px">Tier</td><td style="padding:4px 16px;text-align:right">N</td><td style="padding:4px 16px;text-align:right">Predicted</td><td style="padding:4px 16px;text-align:right">Actual</td><td style="padding:4px 16px;text-align:right">Residual</td></tr>';
  ['must_start','start','borderline','avoid'].forEach(function(tier) {
    var ts = cal.by_tier[tier];
    if (!ts) return;
    var resCls = ts.mean_residual > 0.5 ? 'opp-easy' : (ts.mean_residual < -0.5 ? 'opp-hard' : '');
    h += '<tr><td style="padding:6px 16px"><b>' + (TIER_META[tier] && TIER_META[tier].label || tier) + '</b></td>';
    h += '<td style="padding:6px 16px;text-align:right">' + ts.count + '</td>';
    h += '<td style="padding:6px 16px;text-align:right">' + ts.mean_predicted.toFixed(1) + '</td>';
    h += '<td style="padding:6px 16px;text-align:right">' + ts.mean_actual.toFixed(1) + '</td>';
    h += '<td style="padding:6px 16px;text-align:right" class="' + resCls + '">' + (ts.mean_residual >= 0 ? '+' : '') + ts.mean_residual.toFixed(1) + '</td></tr>';
  });
  h += '</table></div></div>';

  // Top misses
  function renderMissList(title, items, kind) {
    if (!items || !items.length) return '';
    var hh = '<div class="day-card accuracy-card">';
    hh += '<div class="day-header"><span>' + title + '</span></div>';
    hh += '<div class="accuracy-list">';
    items.forEach(function(s) {
      var cls = kind === 'over' ? 'opp-hard' : 'opp-easy';
      hh += '<div class="accuracy-row">';
      hh += '<div class="accuracy-row-main"><b>' + s.name + '</b> ' + (s.opponent || '') + ' &middot; <span style="color:#777">' + s.date + '</span></div>';
      hh += '<div class="accuracy-row-detail">' + (s.tier || '') + ' &middot; predicted ' + (s.predicted_pts || 0).toFixed(1) + ', actual ' + (s.actual_pts || 0).toFixed(1) + ' &middot; <span class="' + cls + '">' + (s.residual >= 0 ? '+' : '') + s.residual.toFixed(1) + '</span></div>';
      hh += '</div>';
    });
    hh += '</div></div>';
    return hh;
  }
  h += renderMissList('Most over-predicted (we said go, they bombed)', cal.worst_overpredictions, 'over');
  h += renderMissList('Best surprises (we underestimated)', cal.best_underpredictions, 'under');

  function renderPolicyBacktest() {
    var p = DECISION_POLICY_BACKTEST || {};
    var h2 = '<div class="day-card accuracy-card">';
    h2 += '<div class="day-header"><span>Decision policy backtest</span><span style="color:#777;font-size:11px">analysis only</span></div>';
    if (!p.available) {
      h2 += '<div class="stream-note" style="color:#777">' + escHtml(p.note || 'Decision policy backtest is not available yet.') + '</div></div>';
      return h2;
    }
    var best = p.best || {};
    var current = p.current || {};
    var deltas = p.deltas || {};
    var diff = p.diff_summary || {};
    h2 += '<div class="decision-summary">';
    h2 += '<span class="decision-pill">Best policy <b>' + escHtml(best.label || 'n/a') + '</b></span>';
    h2 += '<span class="decision-pill">Active overlay <b>' + escHtml(p.active_policy_label || 'n/a') + '</b></span>';
    h2 += '<span class="decision-pill">Rows <b>' + escHtml(p.labeled_rows || 0) + '</b></span>';
    h2 += '<span class="decision-pill">Changed <b>' + escHtml(diff.changed || 0) + '</b></span>';
    h2 += '<span class="decision-pill">Helped/Hurt/Neutral <b>' + escHtml((diff.helped || 0) + '/' + (diff.hurt || 0) + '/' + (diff.neutral || 0)) + '</b></span>';
    h2 += '</div>';
    h2 += '<div class="stream-note" style="margin:0 0 8px;color:#777">';
    h2 += 'Risk guard overlay is active in visible Streaming recommendations when enough bust-risk flags stack up. Projected points and learned corrections are unchanged.';
    if (p.source) {
      h2 += ' Backtest source: ' + escHtml(p.source) + '.';
    }
    h2 += '</div>';
    h2 += '<div class="accuracy-table-wrap"><table class="accuracy-table">';
    h2 += '<tr style="color:#777;font-size:11px;text-transform:uppercase;letter-spacing:0.5px"><td style="padding:4px 16px">Metric</td><td style="padding:4px 16px;text-align:right">Current</td><td style="padding:4px 16px;text-align:right">Best</td><td style="padding:4px 16px;text-align:right">Change</td></tr>';
    var rows = [
      ['START bust rate', current.start_bust_rate, best.start_bust_rate, deltas.start_bust_rate, '%'],
      ['Negative recommended starts', current.negative_recommended, best.negative_recommended, deltas.negative_recommended, ''],
      ['Good starts missed', current.good_starts_missed, best.good_starts_missed, deltas.good_starts_missed, '']
    ];
    rows.forEach(function(row) {
      var isPct = row[4] === '%';
      var cur = Number(row[1] || 0);
      var bst = Number(row[2] || 0);
      var delta = Number(row[3] || 0);
      var dCls = delta < 0 ? 'opp-easy' : (delta > 0 ? 'opp-hard' : '');
      h2 += '<tr><td style="padding:6px 16px"><b>' + escHtml(row[0]) + '</b></td>';
      h2 += '<td style="padding:6px 16px;text-align:right">' + (isPct ? cur.toFixed(1) + '%' : cur.toFixed(0)) + '</td>';
      h2 += '<td style="padding:6px 16px;text-align:right">' + (isPct ? bst.toFixed(1) + '%' : bst.toFixed(0)) + '</td>';
      h2 += '<td style="padding:6px 16px;text-align:right" class="' + dCls + '">' + (delta >= 0 ? '+' : '') + (isPct ? delta.toFixed(1) + ' pts' : delta.toFixed(0)) + '</td></tr>';
    });
    h2 += '</table></div>';
    var reasons = diff.reason_summary || [];
    if (reasons.length) {
      h2 += '<div class="accuracy-list">';
      h2 += '<div class="accuracy-detail" style="margin-bottom:5px">Top risk reasons from the best policy diff:</div>';
      reasons.slice(0, 6).forEach(function(r) {
        h2 += '<div class="accuracy-row">';
        h2 += '<div class="accuracy-row-main"><b>' + escHtml(r.reason || '') + '</b></div>';
        h2 += '<div class="accuracy-row-detail">' + escHtml(r.demotions || 0) + ' demotions &middot; helped ' + escHtml(r.helped || 0) + ' &middot; hurt ' + escHtml(r.hurt || 0) + '</div>';
        h2 += '</div>';
      });
      h2 += '</div>';
    }
    h2 += '<div class="stream-note" style="margin:0;color:#777">' + escHtml(p.note || 'Analysis only. Projected points and scoring are unchanged; visible recommendations may use the active risk guard overlay.') + '</div>';
    h2 += '</div>';
    return h2;
  }
  h += renderPolicyBacktest();

  h += '<div class="stream-note" style="margin:8px 0;color:#777">';
  h += 'Learning uses one selected pregame snapshot per actual start, so duplicate logs and repeated snapshots do not overweight the model.';
  if (LEARNING_SAMPLE_SUMMARY && LEARNING_SAMPLE_SUMMARY.raw_rows !== undefined && LEARNING_SAMPLE_SUMMARY.unique_actual_starts !== undefined) {
    h += ' Latest selection: ' + LEARNING_SAMPLE_SUMMARY.raw_rows + ' raw outcome rows &rarr; ' + LEARNING_SAMPLE_SUMMARY.unique_actual_starts + ' unique starts used for learning.';
  }
  h += '</div>';

  // Emerging candidate signals — close to statistical significance but not
  // yet auto-applied. Lets the user see what's about to kick in.
  if (LEARNED_CANDIDATES && LEARNED_CANDIDATES.length) {
    h += '<div class="day-card accuracy-card">';
    h += '<div class="day-header"><span>Emerging signals (not yet applied)</span><span style="color:#777;font-size:11px">not active until sample, variance, and z-score checks pass</span></div>';
    h += '<div class="accuracy-list">';
    LEARNED_CANDIDATES.forEach(function(b) {
      var dCls = b.mean > 0 ? 'opp-easy' : 'opp-hard';
      var zText = (b.z === null || b.z === undefined) ? 'invalid' : b.z.toFixed(2);
      var reason = b.ineligible_reason ? ' &middot; not eligible: ' + b.ineligible_reason : ' &middot; not eligible yet';
      h += '<div class="accuracy-row" style="display:block">';
      h += '<div style="opacity:0.85">' + b.label + '</div>';
      h += '<div class="accuracy-detail">basis: ' + b.basis + ' &middot; n=' + b.n + ' &middot; ';
      h += 'mean residual <span class="' + dCls + '">' + (b.mean >= 0 ? '+' : '') + (b.mean || 0).toFixed(2) + '</span> &middot; ';
      h += 'std ' + (b.std || 0).toFixed(2) + ' &middot; z ' + zText + reason;
      h += '</div></div>';
    });
    h += '</div></div>';
  }

  // Learned biases — auto-detected feature buckets where the model is off
  var biasKeys = LEARNED_BIASES ? Object.keys(LEARNED_BIASES) : [];
  if (biasKeys.length) {
    h += '<div class="day-card accuracy-card">';
    h += '<div class="day-header"><span>Active learned corrections</span><span style="color:#777;font-size:11px">' + biasKeys.length + ' bucket(s) auto-applied to predictions</span></div>';
    h += '<div class="accuracy-list">';
    var sortedBiases = biasKeys.map(function(k) { return LEARNED_BIASES[k]; })
      .sort(function(a, b) { return Math.abs(b.applied_delta || 0) - Math.abs(a.applied_delta || 0); });
    sortedBiases.forEach(function(b) {
      var dCls = b.mean > 0 ? 'opp-easy' : 'opp-hard';
      var applied = b.applied_delta !== undefined ? b.applied_delta : b.mean;
      var aCls = applied > 0 ? 'opp-easy' : 'opp-hard';
      var zText = (b.z === null || b.z === undefined) ? 'invalid' : b.z.toFixed(2);
      h += '<div class="accuracy-row" style="display:block">';
      h += '<div>' + b.label + '</div>';
      h += '<div class="accuracy-detail">basis: ' + b.basis + ' &middot; n=' + b.n + ' &middot; ';
      h += 'mean residual <span class="' + dCls + '">' + (b.mean >= 0 ? '+' : '') + b.mean.toFixed(2) + '</span> &middot; ';
      h += 'std ' + (b.std || 0).toFixed(2) + ' &middot; z ' + zText + ' &middot; applied <span class="' + aCls + '">' + (applied >= 0 ? '+' : '') + applied.toFixed(2) + '</span>';
      h += '</div></div>';
    });
    h += '</div></div>';
  }

  c.innerHTML = h;
}
renderAccuracy();
</script>
</body>
</html>""")

    # Compute week range label
    week_start, week_end = get_streaming_window()
    try:
        ws = datetime.strptime(week_start, '%Y-%m-%d').strftime('%b %d')
        we = datetime.strptime(week_end, '%Y-%m-%d').strftime('%b %d')
        week_range = f"{ws} - {we}"
    except Exception:
        week_range = f"{week_start} to {week_end}"

    html = html_template.substitute(
        SNAPSHOT_DATE=snapshot_date,
        PREV_LABEL=prev_label,
        PLAYERS_JSON=json.dumps(players_list),
        STREAMING_JSON=json.dumps(streaming_data),
        WEEK_RANGE=week_range,
        MY_ROSTER_COUNT=str(my_roster_count),
        FA_COUNT=str(fa_count),
        RISERS=str(risers),
        FALLERS=str(fallers),
        TRENDING=str(trending_up),
        OLDEST_DATE=oldest_label,
        HOLD_ASOF=hold_asof_label or (date.today() - timedelta(days=1)).strftime('%b %-d'),
        CALIBRATION_JSON=json.dumps(calibration) if calibration else 'null',
        LEARNED_BIASES_JSON=json.dumps(
            learned_biases_override if learned_biases_override is not None else (load_learned_biases() or {})
        ),
        LEARNED_CANDIDATES_JSON=json.dumps(learned_candidates or []),
        LEARNING_SAMPLE_SUMMARY_JSON=json.dumps(learning_sample_summary) if learning_sample_summary else 'null',
        DECISION_POLICY_BACKTEST_JSON=json.dumps(decision_policy_summary) if decision_policy_summary else 'null',
        DAILY_DECISIONS_JSON=json.dumps(daily_decision_summary) if daily_decision_summary else 'null',
        NEXT_WATCHLIST_JSON=json.dumps(next_watchlist_summary) if next_watchlist_summary else 'null',
        ADD_DROP_PRIORITY_JSON=json.dumps(add_drop_priority_summary) if add_drop_priority_summary else 'null',
        MATCHUP_SNAPSHOT_JSON=json.dumps(matchup_snapshot_summary) if matchup_snapshot_summary else 'null',
        MATCHUP_ACTIONS_JSON=json.dumps(matchup_action_summary) if matchup_action_summary else 'null',
        HITTER_DECISIONS_JSON=json.dumps(hitter_decision_summary) if hitter_decision_summary else 'null',
        MATCHUP_EDGE_JSON=json.dumps(matchup_edge_summary) if matchup_edge_summary else 'null',
        FEATURE_LOG_STATUS=feature_log_status_override or prediction_feature_log_status(),
        TOP_BANNER_HTML=top_banner_html or '',
    )

    if skip_unchanged_write and os.path.exists(OUTPUT_HTML):
        try:
            with open(OUTPUT_HTML) as f:
                if f.read() == html:
                    print(f"Report unchanged at {OUTPUT_HTML}")
                    print(f"  Open in browser: file://{OUTPUT_HTML}")
                    return
        except Exception:
            pass

    with open(OUTPUT_HTML, 'w') as f:
        f.write(html)
    print(f"Report saved to {OUTPUT_HTML}")
    print(f"  Open in browser: file://{OUTPUT_HTML}")


# =============================================================================
# SETUP
# =============================================================================

def run_setup():
    print("ESPN Authentication Setup")
    print("=" * 50)
    print("\nTo get your ESPN cookies:")
    print("  1. Go to fantasy.espn.com in Chrome")
    print("  2. Open DevTools (Cmd+Option+I)")
    print("  3. Go to Application > Cookies > fantasy.espn.com")
    print("  4. Find 'espn_s2' and 'SWID' cookies")
    print("  5. Copy their values below\n")

    espn_s2 = input("espn_s2 cookie value: ").strip()
    swid = input("SWID cookie value: ").strip()

    if not espn_s2 or not swid:
        print("Both values are required.")
        return

    config = {'espn_s2': espn_s2, 'SWID': swid}
    with open(CONFIG_FILE, 'w') as f:
        json.dump(config, f, indent=2)
    print(f"\nSaved to {CONFIG_FILE}")
    print("You can now run: python3.11 fantasy_tracker.py")


# =============================================================================
# PREDICTION LEARNING — log predictions, fetch outcomes, compute residuals
# =============================================================================

PREDICTIONS_DIR = os.path.join(SCRIPT_DIR, 'predictions')
PREDICTIONS_ARCHIVE_DIR = os.path.join(SCRIPT_DIR, 'predictions_archive')
OUTCOMES_LOG = os.path.join(SCRIPT_DIR, 'predictions_outcomes.jsonl')
LEARNED_BIASES_PATH = os.path.join(SCRIPT_DIR, 'learned_biases.json')

# Buffer predictions in memory and write one JSONL file per date at the end
# of the run. Avoids thousands of small files which slow git operations to
# a crawl (each `git add` indexes every file).
_pending_predictions = {}  # {(game_date, pitcher_norm): record}

# Feature bucket definitions for bias detection
OPP_RANK_BRACKETS = [
    (1, 5, 'top-5 OPS offenses'),
    (6, 10, 'top-10 OPS offenses'),
    (11, 20, 'middle-tier offenses'),
    (21, 25, 'bottom-10 OPS offenses'),
    (26, 30, 'bottom-5 OPS offenses'),
]

PARK_BRACKETS = [
    (0.0, 0.96, 'pitcher-friendly parks'),
    (0.96, 1.04, 'neutral parks'),
    (1.04, 99.0, 'hitter-friendly parks'),
]


# =============================================================================
# WAREHOUSE FOUNDATION — parallel to existing JSON/JSONL state
# =============================================================================

def warehouse_enabled():
    """Return True when optional DuckDB/Parquet dependencies are importable."""
    try:
        import duckdb  # noqa: F401
        import pyarrow  # noqa: F401
        return True
    except Exception:
        return False


def wh_path(*parts):
    """Build a path under engine/warehouse without touching existing JSON state."""
    return os.path.join(WAREHOUSE_DIR, *parts)


def _ensure_warehouse_dirs():
    for layer in WAREHOUSE_LAYERS:
        os.makedirs(wh_path(layer), exist_ok=True)


def _warehouse_parquet_files(*parts):
    base = wh_path(*parts)
    if not os.path.isdir(base):
        return []
    out = []
    for root, _, files in os.walk(base):
        for fn in files:
            if fn.endswith('.parquet'):
                out.append(os.path.join(root, fn))
    return sorted(out)


def wh_write_parquet(data, *parts):
    """Write a dataframe-like object to Parquet. Not used by production flow yet."""
    _ensure_warehouse_dirs()
    path = wh_path(*parts)
    os.makedirs(os.path.dirname(path), exist_ok=True)
    df = data if isinstance(data, pd.DataFrame) else pd.DataFrame(data)
    df.to_parquet(path, index=False)
    return path


def wh_read_parquet(*parts):
    """Read a warehouse Parquet file into a dataframe."""
    return pd.read_parquet(wh_path(*parts))


def _scalar_for_parquet(value):
    if isinstance(value, (dict, list, tuple)):
        return json.dumps(value, sort_keys=True)
    return value


def _merge_feature_columns_for_warehouse(row, features, blocked=None):
    """Merge prediction features as plain columns; prefix only true collisions."""
    blocked = set(blocked or [])
    for key in FEATURE_REGISTRY:
        if key not in blocked:
            row.setdefault(key, None)
    for key, value in (features or {}).items():
        if key in blocked:
            continue
        if key in FEATURE_REGISTRY or key not in row:
            # Registered model features own their plain column name. If a
            # top-level record also has that key, prefer the prediction-log
            # feature value because it is the model input being audited.
            row[key] = _scalar_for_parquet(value)
        else:
            row[f'feature_{key}'] = _scalar_for_parquet(value)
    return row


SP_START_EXCLUDED_LABEL_COLUMNS = {
    'actual_pts', 'actual_ip', 'actual_k', 'actual_er', 'actual_win',
    'actual_line', 'residual', 'residual_raw', 'no_start',
}
SP_START_OUTPUT_COLUMNS = {
    'predicted_pts', 'predicted_pts_raw', 'final_pts',
}
TRAINING_LABEL_COLUMNS = {
    'actual_pts', 'actual_ip', 'actual_k', 'actual_er', 'actual_bb',
    'actual_hits', 'actual_hr', 'actual_win', 'residual',
}


def _start_id_for_record(record):
    return '|'.join([
        str(record.get('date') or record.get('game_date') or ''),
        normalize_name(record.get('name') or record.get('pitcher_name') or ''),
        str(record.get('team') or ''),
        str(record.get('opponent') or ''),
        str(record.get('home_away') or ''),
    ])


def _prediction_record_to_wh_row(record):
    """Flatten one prediction JSONL record into warehouse-friendly columns."""
    features = _features_with_weather_metadata(record.get('features') or {}, record)
    row = {
        'start_id': _start_id_for_record(record),
        'game_date': record.get('date'),
        'logged_at': record.get('logged_at'),
        'snapshot_time': record.get('snapshot_time'),
        'pitcher_name': record.get('name'),
        'pitcher_id': record.get('pitcher_id'),
        'team': record.get('team'),
        'opponent': record.get('opponent'),
        'status': record.get('status'),
        'predicted_pts': record.get('predicted_pts'),
        'predicted_pts_raw': record.get('predicted_pts_raw'),
        'final_pts': record.get('final_pts'),
    }
    for key, value in record.items():
        if key == 'features':
            continue
        if key not in row:
            row[key] = _scalar_for_parquet(value)
    return _merge_feature_columns_for_warehouse(row, features)


def wh_write_prediction_parquet(game_date, records):
    """Mirror prediction JSONL records to one flat Parquet file per game date."""
    rows = [_prediction_record_to_wh_row(rec) for rec in records]
    return wh_write_parquet(rows, 'predictions', f'{game_date}.parquet')


def _prediction_jsonl_files_by_date(directory):
    """Map prediction JSONL partition dates to paths under one directory."""
    files = {}
    if not os.path.isdir(directory):
        return files
    for fn in sorted(os.listdir(directory)):
        if fn.endswith('.jsonl'):
            files[fn[:-len('.jsonl')]] = os.path.join(directory, fn)
    return files


def _read_prediction_jsonl_files_by_date(files_by_date):
    """Read selected prediction JSONL files without mutating source files."""
    records_by_date = {}
    skipped = 0
    for game_date, path in sorted(files_by_date.items()):
        try:
            with open(path) as f:
                for line in f:
                    if not line.strip():
                        continue
                    try:
                        rec = json.loads(line)
                    except Exception:
                        skipped += 1
                        continue
                    records_by_date.setdefault(game_date, []).append(rec)
        except Exception as e:
            skipped += 1
            print(f"  Skipped prediction partition {path}: {type(e).__name__}: {e}")
    return records_by_date, skipped


def _prediction_records_by_jsonl_date():
    """Read current prediction JSONL partitions without mutating source files."""
    return _read_prediction_jsonl_files_by_date(_prediction_jsonl_files_by_date(PREDICTIONS_DIR))


def _backfill_warehouse_feature_partitions(records_by_date, source_label, skipped=0,
                                           archive_files=None, current_files=None):
    prediction_paths = []
    feature_paths = []
    prediction_rows = 0
    feature_rows = 0
    dates = sorted(records_by_date)
    for game_date in dates:
        records = records_by_date[game_date]
        prediction_paths.append(wh_write_prediction_parquet(game_date, records))
        feature_paths.append(wh_write_sp_start_features_parquet(game_date, records))
        prediction_rows += len(records)
        feature_rows += len(records)

    print("Warehouse feature backfill complete")
    print(f"  Source: {source_label}")
    if archive_files is not None:
        print(f"  Archive files found: {len(archive_files)}")
        for d in sorted(archive_files):
            print(f"    archive {d}: {archive_files[d]}")
    if current_files is not None:
        print(f"  Current files found: {len(current_files)}")
        for d in sorted(current_files):
            print(f"    current {d}: {current_files[d]}")
    print(f"  Dates backfilled: {', '.join(dates) if dates else 'None'}")
    print(f"  Prediction rows backfilled: {prediction_rows}")
    print(f"  SP start feature rows backfilled: {feature_rows}")
    print(f"  Date partitions written: {len(records_by_date)}")
    print(f"  Prediction destination: {wh_path('predictions')}")
    print(f"  Feature destination: {wh_path('features', 'sp_start_features')}")
    if skipped:
        print(f"  Skipped malformed/unreadable rows or files: {skipped}")
    return {
        'prediction_rows': prediction_rows,
        'feature_rows': feature_rows,
        'dates': len(records_by_date),
        'date_values': dates,
        'skipped': skipped,
        'prediction_paths': prediction_paths,
        'feature_paths': feature_paths,
    }


def backfill_warehouse_features():
    """Rebuild prediction and SP feature Parquet partitions from prediction JSONL."""
    records_by_date, skipped = _prediction_records_by_jsonl_date()
    return _backfill_warehouse_feature_partitions(
        records_by_date,
        f"{PREDICTIONS_DIR}/*.jsonl",
        skipped=skipped,
    )


def backfill_warehouse_features_from_archive():
    """Rebuild prediction/SP feature Parquet from archive plus current JSONL."""
    archive_files = _prediction_jsonl_files_by_date(PREDICTIONS_ARCHIVE_DIR)
    current_files = _prediction_jsonl_files_by_date(PREDICTIONS_DIR)
    selected_files = dict(archive_files)
    selected_files.update(current_files)  # Current prediction files win date conflicts.
    records_by_date, skipped = _read_prediction_jsonl_files_by_date(selected_files)
    return _backfill_warehouse_feature_partitions(
        records_by_date,
        f"{PREDICTIONS_ARCHIVE_DIR}/*.jsonl + {PREDICTIONS_DIR}/*.jsonl",
        skipped=skipped,
        archive_files=archive_files,
        current_files=current_files,
    )


def _outcome_record_to_wh_row(record):
    """Flatten one joined outcome JSONL record into warehouse-friendly columns."""
    features = _features_with_venue_metadata(record.get('features') or {}, record)
    actual_line = record.get('actual_line') or {}
    row = {
        'start_id': _start_id_for_record(record),
        'game_date': record.get('date'),
        'pitcher_name': record.get('name'),
        'pitcher_id': record.get('pitcher_id'),
        'team': record.get('team'),
        'opponent': record.get('opponent'),
        'status': record.get('status'),
        'predicted_pts': record.get('predicted_pts'),
        'predicted_pts_raw': record.get('predicted_pts_raw'),
        'final_pts': record.get('final_pts'),
        'actual_pts': record.get('actual_pts'),
        'residual': record.get('residual'),
        'residual_raw': record.get('residual_raw'),
        'no_start': record.get('no_start'),
    }
    for key, value in record.items():
        if key in ('features', 'actual_line'):
            continue
        if key not in row:
            row[key] = _scalar_for_parquet(value)
    row['actual_line'] = _scalar_for_parquet(actual_line) if actual_line else None
    for key, value in actual_line.items():
        row[f'actual_{key.lower()}'] = _scalar_for_parquet(value)
    return _merge_feature_columns_for_warehouse(row, features)


def _outcome_records_for_date(game_date):
    records = []
    if not os.path.exists(OUTCOMES_LOG):
        return records
    try:
        with open(OUTCOMES_LOG) as f:
            for line in f:
                if not line.strip():
                    continue
                try:
                    rec = json.loads(line)
                except Exception:
                    continue
                if rec.get('date') == game_date:
                    records.append(rec)
    except Exception:
        return []
    return records


def wh_write_outcome_parquet(game_date):
    """Mirror joined outcome JSONL rows to one flat Parquet file per game date."""
    if PREVIEW_LOCAL:
        return None
    rows = [_outcome_record_to_wh_row(rec) for rec in _outcome_records_for_date(game_date)]
    if not rows:
        return None
    return wh_write_parquet(rows, 'outcomes', f'{game_date}.parquet')


def backfill_warehouse_outcomes():
    """Rebuild outcome Parquet partitions from the JSONL source of truth."""
    records_by_date = {}
    skipped = 0
    if not os.path.exists(OUTCOMES_LOG):
        print(f"No outcomes log found: {OUTCOMES_LOG}")
        return {'rows': 0, 'dates': 0, 'skipped': 0, 'paths': []}
    try:
        with open(OUTCOMES_LOG) as f:
            for line in f:
                if not line.strip():
                    continue
                try:
                    rec = json.loads(line)
                except Exception:
                    skipped += 1
                    continue
                game_date = rec.get('date') or rec.get('game_date')
                if not game_date:
                    skipped += 1
                    continue
                records_by_date.setdefault(game_date, []).append(rec)
    except Exception as e:
        print(f"Outcome backfill failed to read {OUTCOMES_LOG}: {e}")
        return {'rows': 0, 'dates': 0, 'skipped': skipped, 'paths': []}

    paths = []
    total_rows = 0
    for game_date in sorted(records_by_date):
        rows = [_outcome_record_to_wh_row(rec) for rec in records_by_date[game_date]]
        rows.sort(key=lambda row: (
            str(row.get('start_id') or ''),
            str(row.get('snapshot_time') or row.get('logged_at') or ''),
            str(row.get('pitcher_name') or ''),
            str(row.get('team') or ''),
            str(row.get('opponent') or ''),
        ))
        path = wh_write_parquet(rows, 'outcomes', f'{game_date}.parquet')
        paths.append(path)
        total_rows += len(rows)

    print("Warehouse outcome backfill complete")
    print(f"  Source: {OUTCOMES_LOG}")
    print(f"  Rows backfilled: {total_rows}")
    print(f"  Date partitions written: {len(paths)}")
    print(f"  Destination: {wh_path('outcomes')}")
    if skipped:
        print(f"  Skipped malformed/undated rows: {skipped}")
    return {'rows': total_rows, 'dates': len(paths), 'skipped': skipped, 'paths': paths}


def _sp_start_feature_record_to_wh_row(record):
    """Flatten one prediction record into pregame-only SP start features."""
    features = _features_with_weather_metadata(record.get('features') or {}, record)
    game_date = record.get('date')
    snapshot_time = record.get('snapshot_time') or record.get('logged_at')
    pitcher_name = record.get('name')
    row = {
        'start_id': _start_id_for_record(record),
        'game_id': record.get('game_id') or record.get('game_pk'),
        'game_date': game_date,
        'snapshot_time': snapshot_time,
        'logged_at': record.get('logged_at'),
        'pitcher_name': pitcher_name,
        'pitcher_id': record.get('pitcher_id'),
        'team': record.get('team'),
        'opponent': record.get('opponent'),
        'home_away': record.get('home_away'),
        'status': record.get('status'),
        'lineup_status': record.get('lineup_status'),
        'probable_status': record.get('probable_status'),
        'tier': record.get('tier'),
        'base_pts': record.get('base_pts'),
        'learned_adj_total': record.get('adj_total'),
        'learned_adjustments': _scalar_for_parquet(record.get('adjustments', [])),
    }
    blocked = SP_START_EXCLUDED_LABEL_COLUMNS | SP_START_OUTPUT_COLUMNS | {'features'}
    for key, value in record.items():
        if key in blocked or key in row:
            continue
        row[key] = _scalar_for_parquet(value)
    return _merge_feature_columns_for_warehouse(row, features, blocked=blocked)


def wh_write_sp_start_features_parquet(game_date, records):
    """Write pregame-only model-ready SP start features, sourced from predictions."""
    rows = [_sp_start_feature_record_to_wh_row(rec) for rec in records]
    return wh_write_parquet(rows, 'features', 'sp_start_features', f'{game_date}.parquet')


def _duckdb_ident(name):
    safe = re.sub(r'[^0-9A-Za-z_]+', '_', name).strip('_').lower()
    if not safe:
        safe = 'parquet_view'
    if safe[0].isdigit():
        safe = f'v_{safe}'
    return safe


def _sql_path(path):
    return path.replace("'", "''")


def _table_columns(conn, table_name):
    try:
        rows = conn.execute(f'DESCRIBE "{table_name}"').fetchall()
        return {row[0] for row in rows}
    except Exception:
        return set()


def _sql_label_expr(cols, name, fallback=None):
    if name in cols:
        return f'o."{name}" AS "{name}"'
    if fallback and fallback in cols:
        return f'o."{fallback}" AS "{name}"'
    return f'NULL AS "{name}"'


def _create_training_sp_starts_view(conn):
    """Create analysis-only training view from pregame features + outcomes."""
    feature_files = _warehouse_parquet_files('features', 'sp_start_features')
    outcome_files = _warehouse_parquet_files('outcomes')
    if not feature_files:
        conn.execute("""
            CREATE OR REPLACE VIEW training_sp_starts AS
            SELECT
              NULL::VARCHAR AS start_id,
              NULL::VARCHAR AS snapshot_time,
              NULL::VARCHAR AS game_date,
              NULL::VARCHAR AS pitcher_name,
              NULL::VARCHAR AS team,
              NULL::VARCHAR AS opponent,
              NULL::DOUBLE AS actual_pts,
              NULL::DOUBLE AS actual_ip,
              NULL::DOUBLE AS actual_k,
              NULL::DOUBLE AS actual_er,
              NULL::DOUBLE AS actual_bb,
              NULL::DOUBLE AS actual_hits,
              NULL::DOUBLE AS actual_hr,
              NULL::INTEGER AS actual_win,
              NULL::DOUBLE AS residual,
              FALSE AS has_label
            WHERE FALSE
        """)
        return

    feature_glob = _sql_path(os.path.join(wh_path('features', 'sp_start_features'), '*.parquet'))
    conn.execute(
        "CREATE OR REPLACE VIEW sp_start_features AS "
        f"SELECT * FROM read_parquet('{feature_glob}', union_by_name=true)"
    )
    feature_cols = _table_columns(conn, 'sp_start_features')

    if not outcome_files:
        conn.execute("""
            CREATE OR REPLACE VIEW training_sp_starts AS
            SELECT
              f.*,
              NULL AS actual_pts,
              NULL AS actual_ip,
              NULL AS actual_k,
              NULL AS actual_er,
              NULL AS actual_bb,
              NULL AS actual_hits,
              NULL AS actual_hr,
              NULL AS actual_win,
              NULL AS residual,
              FALSE AS has_label
            FROM sp_start_features f
        """)
        return

    outcome_glob = _sql_path(os.path.join(wh_path('outcomes'), '*.parquet'))
    conn.execute(
        "CREATE OR REPLACE VIEW warehouse_outcomes AS "
        f"SELECT * FROM read_parquet('{outcome_glob}', union_by_name=true)"
    )
    outcome_cols = _table_columns(conn, 'warehouse_outcomes')
    join_clauses = []
    if 'start_id' in feature_cols and 'start_id' in outcome_cols:
        join_clauses.append('f.start_id = o.start_id')
    elif {'game_date', 'pitcher_name', 'team', 'opponent'}.issubset(feature_cols) and {
        'game_date', 'pitcher_name', 'team', 'opponent'
    }.issubset(outcome_cols):
        join_clauses.append(
            "(f.game_date = o.game_date "
            "AND lower(coalesce(f.pitcher_name, '')) = lower(coalesce(o.pitcher_name, '')) "
            "AND coalesce(f.team, '') = coalesce(o.team, '') "
            "AND coalesce(f.opponent, '') = coalesce(o.opponent, ''))"
        )
    join_sql = ' OR '.join(join_clauses) if join_clauses else 'FALSE'

    if 'actual_win' in outcome_cols:
        actual_win_expr = 'try_cast(o."actual_win" AS INTEGER) AS "actual_win"'
    elif 'actual_decision' in outcome_cols:
        actual_win_expr = (
            "CASE WHEN o.\"actual_decision\" = 'W' THEN 1 "
            "WHEN o.\"actual_decision\" IS NOT NULL THEN 0 "
            "ELSE NULL END AS \"actual_win\""
        )
    else:
        actual_win_expr = 'NULL AS "actual_win"'

    label_exprs = [
        _sql_label_expr(outcome_cols, 'actual_pts'),
        _sql_label_expr(outcome_cols, 'actual_ip'),
        _sql_label_expr(outcome_cols, 'actual_k'),
        _sql_label_expr(outcome_cols, 'actual_er'),
        _sql_label_expr(outcome_cols, 'actual_bb'),
        _sql_label_expr(outcome_cols, 'actual_hits', fallback='actual_h'),
        _sql_label_expr(outcome_cols, 'actual_hr'),
        actual_win_expr,
        _sql_label_expr(outcome_cols, 'residual'),
    ]
    labels_sql = ',\n              '.join(label_exprs)
    conn.execute(f"""
        CREATE OR REPLACE VIEW training_sp_starts AS
        SELECT
          f.*,
          {labels_sql},
          o.game_date IS NOT NULL AS has_label
        FROM sp_start_features f
        LEFT JOIN warehouse_outcomes o
          ON {join_sql}
    """)


def wh_conn(database=':memory:'):
    """Create a DuckDB connection with views over existing warehouse Parquet files."""
    import duckdb

    _ensure_warehouse_dirs()
    conn = duckdb.connect(database=database)
    for layer in WAREHOUSE_LAYERS:
        layer_dir = wh_path(layer)
        for root, _, files in os.walk(layer_dir):
            for fn in files:
                if not fn.endswith('.parquet'):
                    continue
                path = os.path.join(root, fn)
                rel = os.path.relpath(path, WAREHOUSE_DIR)
                view = _duckdb_ident(os.path.splitext(rel)[0])
                escaped_path = path.replace("'", "''")
                conn.execute(
                    f'CREATE OR REPLACE VIEW "{view}" AS '
                    f"SELECT * FROM read_parquet('{escaped_path}')"
                )
    _create_training_sp_starts_view(conn)
    return conn


def audit_warehouse():
    """Audit the inert DuckDB/Parquet warehouse foundation."""
    missing = []
    for layer in WAREHOUSE_LAYERS:
        path = wh_path(layer)
        exists = os.path.isdir(path)
        if not exists:
            missing.append(layer)

    duckdb_ok = False
    duckdb_error = None
    views = []
    try:
        conn = wh_conn()
        views = conn.execute(
            "SELECT table_name FROM information_schema.tables "
            "WHERE table_type = 'VIEW' ORDER BY table_name"
        ).fetchall()
        conn.close()
        duckdb_ok = True
    except Exception as e:
        duckdb_error = e

    json_counts = _prediction_source_jsonl_counts_by_date()
    parquet_counts = _prediction_parquet_counts_by_date()
    missing_parquet = sorted(set(json_counts) - set(parquet_counts))
    json_dupes = _prediction_source_jsonl_duplicate_counts_by_date()
    parquet_dupes = _prediction_parquet_duplicate_counts_by_date()

    outcome_json_counts = _outcome_jsonl_counts_by_date()
    outcome_parquet_counts = _outcome_parquet_counts_by_date()
    outcome_missing_parquet = sorted(set(outcome_json_counts) - set(outcome_parquet_counts))
    outcome_json_dupes = _outcome_jsonl_duplicate_counts_by_date()
    outcome_parquet_dupes = _outcome_parquet_duplicate_counts_by_date()
    learning_jsonl_stats, learning_parquet_stats = _learning_outcome_source_counts()

    feature_counts = _sp_start_feature_counts_by_date()
    feature_dupes = _sp_start_feature_duplicate_counts_by_date()
    feature_columns = _sp_start_feature_columns()
    feature_duplicate_style_columns = _duplicate_style_feature_columns(feature_columns)
    leakage_columns = _sp_start_feature_leakage_columns(feature_columns)
    training = _training_sp_starts_stats() if duckdb_ok else {
        'rows': 0,
        'rows_with_labels': 0,
        'rows_without_labels': 0,
        'duplicate_join_keys': 0,
        'join_key_audit': 'DuckDB initialization failed',
        'possible_leakage_columns': [],
    }
    training_leakage = training['possible_leakage_columns']

    prediction_total_json = sum(json_counts.values())
    prediction_total_parquet = sum(parquet_counts.values())
    outcome_total_json = sum(outcome_json_counts.values())
    outcome_total_parquet = sum(outcome_parquet_counts.values())
    feature_total = sum(feature_counts.values())
    feature_dates = sorted(d for d, n in feature_counts.items() if n)
    outcome_label_counts = outcome_parquet_counts or outcome_json_counts
    outcome_dates = sorted(d for d, n in outcome_label_counts.items() if n)
    labels_pending_for_future_games = (
        bool(feature_dates)
        and bool(outcome_dates)
        and training['rows'] > 0
        and training['rows_with_labels'] == 0
        and min(feature_dates) > max(outcome_dates)
    )
    warning_reasons = []

    if not duckdb_ok or missing:
        warehouse_status = 'FAIL'
    else:
        warehouse_status = 'OK'

    if not json_counts:
        prediction_message = 'No prediction JSONL rows found yet'
    elif missing_parquet or prediction_total_json != prediction_total_parquet:
        prediction_message = 'Predictions not fully mirrored yet'
        warning_reasons.append(prediction_message)
    else:
        prediction_message = 'Predictions mirrored correctly'

    if not outcome_json_counts:
        outcome_message = 'No outcome JSONL rows found yet'
    elif outcome_missing_parquet and outcome_total_parquet == 0:
        outcome_message = 'Outcomes not mirrored yet'
        warning_reasons.append(outcome_message)
    elif outcome_missing_parquet or outcome_total_json != outcome_total_parquet:
        outcome_message = 'Outcomes not fully mirrored yet'
        warning_reasons.append(outcome_message)
    else:
        outcome_message = 'Outcomes mirrored correctly'
    if (
            learning_parquet_stats['unique_actual_starts']
            and learning_jsonl_stats['unique_actual_starts'] != learning_parquet_stats['unique_actual_starts']):
        warning_reasons.append(
            "Learning input count mismatch: "
            f"jsonl={learning_jsonl_stats['unique_actual_starts']} "
            f"parquet={learning_parquet_stats['unique_actual_starts']}"
        )

    if feature_total:
        feature_message = 'Feature table has rows'
        if feature_duplicate_style_columns:
            feature_message += '; duplicate-style columns found'
            warning_reasons.append('Feature table has duplicate-style columns')
    else:
        feature_message = 'Feature table has no rows yet'
        warning_reasons.append(feature_message)

    if training['rows_with_labels']:
        training_message = 'Training view has labeled rows'
    elif labels_pending_for_future_games:
        training_message = (
            'Training labels pending: feature rows are for games after '
            'the latest available outcome date.'
        )
    elif training['rows']:
        training_message = 'Training view has feature rows but no labels yet'
        warning_reasons.append(training_message)
    else:
        training_message = 'Training view has no rows yet'
        warning_reasons.append(training_message)

    if leakage_columns or training_leakage:
        leakage_message = 'Possible leakage columns found'
        warning_reasons.append(leakage_message)
    else:
        leakage_message = 'No obvious leakage columns found'

    if warehouse_status != 'FAIL' and warning_reasons:
        warehouse_status = 'WARNING'
    elif warehouse_status != 'FAIL' and labels_pending_for_future_games:
        warehouse_status = 'OK_WITH_PENDING_LABELS'

    print("WAREHOUSE AUDIT")
    print("=" * 60)
    print("Summary")
    print(f"  Warehouse status: {warehouse_status}")
    print(f"  Prediction mirror status: {prediction_message}")
    print(f"  Outcome mirror status: {outcome_message}")
    print(f"  sp_start_features status: {feature_message}")
    print(f"  training view status: {training_message}")
    print(f"  leakage status: {leakage_message}")

    print("\nDetailed audit")
    print(f"Warehouse root: {WAREHOUSE_DIR}")

    for layer in WAREHOUSE_LAYERS:
        path = wh_path(layer)
        exists = os.path.isdir(path)
        print(f"  {layer:11s} {'OK' if exists else 'MISSING'}  {path}")

    if missing:
        print(f"\nMissing warehouse folders: {', '.join(missing)}")
    else:
        print("\nWarehouse folders: OK")

    if duckdb_ok:
        print("DuckDB initialization: OK")
        print(f"Parquet views available: {len(views)}")
        for (name,) in views:
            print(f"  - {name}")
    else:
        print(f"DuckDB initialization: FAILED ({type(duckdb_error).__name__}: {duckdb_error})")
        raise SystemExit(1)

    print("\nPrediction row counts by date")
    all_dates = sorted(set(json_counts) | set(parquet_counts))
    if not all_dates:
        print("  None")
    for d in all_dates:
        print(f"  {d}: jsonl={json_counts.get(d, 0)} parquet={parquet_counts.get(d, 0)}")
    print(f"Total prediction rows: jsonl={sum(json_counts.values())} parquet={sum(parquet_counts.values())}")

    print("\nMissing Parquet prediction dates")
    if missing_parquet:
        for d in missing_parquet:
            print(f"  - {d}")
    else:
        print("  None")

    print("\nDuplicate prediction rows")
    any_dupes = False
    for d in sorted(set(json_dupes) | set(parquet_dupes)):
        jd = json_dupes.get(d, 0)
        pdp = parquet_dupes.get(d, 0)
        if jd or pdp:
            any_dupes = True
            print(f"  {d}: jsonl={jd} parquet={pdp}")
    if not any_dupes:
        print("  None detected")

    print("\nOutcome row counts by date")
    all_outcome_dates = sorted(set(outcome_json_counts) | set(outcome_parquet_counts))
    if not all_outcome_dates:
        print("  None")
    for d in all_outcome_dates:
        print(f"  {d}: jsonl={outcome_json_counts.get(d, 0)} parquet={outcome_parquet_counts.get(d, 0)}")
    print(f"Total outcome rows: jsonl={sum(outcome_json_counts.values())} parquet={sum(outcome_parquet_counts.values())}")

    print("\nMissing Parquet outcome dates")
    if outcome_missing_parquet:
        for d in outcome_missing_parquet:
            print(f"  - {d}")
    else:
        print("  None")

    print("\nDuplicate outcome rows")
    any_outcome_dupes = False
    for d in sorted(set(outcome_json_dupes) | set(outcome_parquet_dupes)):
        jd = outcome_json_dupes.get(d, 0)
        pdp = outcome_parquet_dupes.get(d, 0)
        if jd or pdp:
            any_outcome_dupes = True
            print(f"  {d}: jsonl={jd} parquet={pdp}")
    if not any_outcome_dupes:
        print("  None detected")

    print("\nLearning input outcome counts")
    print(f"  JSONL raw rows: {learning_jsonl_stats['raw_rows']}")
    print(f"  JSONL exact duplicates removed for learning: {learning_jsonl_stats['exact_duplicates_removed']}")
    print(f"  JSONL rows after exact dedupe eligible for learning: {learning_jsonl_stats['eligible_rows_after_exact_dedupe']}")
    print(f"  JSONL unique actual starts used for learning: {learning_jsonl_stats['unique_actual_starts']}")
    print(f"  JSONL snapshot groups collapsed for learning: {learning_jsonl_stats['snapshot_groups_collapsed']}")
    if learning_parquet_stats['raw_rows']:
        print(f"  Parquet raw rows: {learning_parquet_stats['raw_rows']}")
        print(f"  Parquet unique actual starts used for learning: {learning_parquet_stats['unique_actual_starts']}")
        if learning_jsonl_stats['unique_actual_starts'] == learning_parquet_stats['unique_actual_starts']:
            print("  OK: JSONL and Parquet learning inputs match")
        else:
            print("  WARNING: JSONL and Parquet learning inputs differ")
    else:
        print("  Parquet raw rows: 0")
        print("  Learning scan will use JSONL fallback")

    print("\nSP start feature row counts by date")
    if not feature_counts:
        print("  None")
    for d in sorted(feature_counts):
        print(f"  {d}: rows={feature_counts[d]}")
    print(f"Total SP start feature rows: {sum(feature_counts.values())}")
    if feature_dates:
        print(f"SP start feature date range: {feature_dates[0]} through {feature_dates[-1]}")
    else:
        print("SP start feature date range: None")

    print("\nSP start feature uniqueness")
    any_feature_dupes = False
    for d in sorted(feature_dupes):
        if feature_dupes[d]:
            any_feature_dupes = True
            print(f"  {d}: duplicate start_id + snapshot_time rows={feature_dupes[d]}")
    if not any_feature_dupes:
        print("  OK: one row per start_id + snapshot_time")

    print("\nSP start feature leakage columns")
    if leakage_columns:
        for col in leakage_columns:
            print(f"  - {col}")
    else:
        print("  None detected")

    print("\nSP start feature duplicate-style columns")
    if feature_duplicate_style_columns:
        print("  These usually mean an older Parquet partition has both a plain feature column and a feature_ copy.")
        for plain, prefixed in feature_duplicate_style_columns:
            print(f"  - {plain} and {prefixed}")
    else:
        print("  None detected")

    print("\nSP start feature null-heavy columns (threshold >= 70%)")
    null_heavy_features = _sp_start_feature_null_heavy()
    if null_heavy_features:
        for col, n_null, total, pct in null_heavy_features[:40]:
            print(f"  - {col}: {pct}% null/missing ({n_null}/{total})")
    else:
        print("  None")

    print("\nSP start feature weather/venue/roof coverage")
    weather_coverage = _sp_start_feature_weather_coverage()
    if weather_coverage:
        for col, populated, total, pct in weather_coverage:
            print(f"  - {col}: {pct}% populated ({populated}/{total})")
    else:
        print("  None")

    print("\nSP start feature workload/leash coverage")
    workload_coverage = _sp_start_feature_workload_coverage()
    if workload_coverage:
        for col, populated, total, pct in workload_coverage:
            print(f"  - {col}: {pct}% populated ({populated}/{total})")
    else:
        print("  None")

    print("\nTraining view training_sp_starts")
    print(f"  rows: {training['rows']}")
    print(f"  rows with labels: {training['rows_with_labels']}")
    print(f"  rows without labels: {training['rows_without_labels']}")
    print(f"  duplicate join keys: {training['duplicate_join_keys']}")
    print(f"  join key audit: {training['join_key_audit']}")
    if outcome_dates:
        print(f"  latest available outcome date: {outcome_dates[-1]}")
    else:
        print("  latest available outcome date: None")
    if labels_pending_for_future_games:
        print("  label explanation: feature rows are for games after the latest available outcome date")

    print("\nTraining view possible leakage columns")
    if training['possible_leakage_columns']:
        for col in training['possible_leakage_columns']:
            print(f"  - {col}")
    else:
        print("  None detected")


def _prediction_jsonl_counts_by_date():
    counts = {}
    if not os.path.isdir(PREDICTIONS_DIR):
        return counts
    for fn in sorted(os.listdir(PREDICTIONS_DIR)):
        if not fn.endswith('.jsonl'):
            continue
        game_date = fn[:-len('.jsonl')]
        path = os.path.join(PREDICTIONS_DIR, fn)
        n = 0
        try:
            with open(path) as f:
                for line in f:
                    if line.strip():
                        n += 1
        except Exception:
            n = 0
        counts[game_date] = n
    return counts


def _prediction_source_jsonl_counts_by_date():
    counts = {}
    files = _prediction_jsonl_files_by_date(PREDICTIONS_ARCHIVE_DIR)
    files.update(_prediction_jsonl_files_by_date(PREDICTIONS_DIR))
    for game_date, path in sorted(files.items()):
        n = 0
        try:
            with open(path) as f:
                for line in f:
                    if line.strip():
                        n += 1
        except Exception:
            n = 0
        counts[game_date] = n
    return counts


def _prediction_parquet_counts_by_date():
    counts = {}
    pred_dir = wh_path('predictions')
    if not os.path.isdir(pred_dir):
        return counts
    for fn in sorted(os.listdir(pred_dir)):
        if not fn.endswith('.parquet'):
            continue
        game_date = fn[:-len('.parquet')]
        try:
            df = wh_read_parquet('predictions', fn)
            counts[game_date] = len(df)
        except Exception:
            counts[game_date] = 0
    return counts


def _prediction_jsonl_duplicate_counts_by_date():
    dupes = {}
    if not os.path.isdir(PREDICTIONS_DIR):
        return dupes
    for fn in sorted(os.listdir(PREDICTIONS_DIR)):
        if not fn.endswith('.jsonl'):
            continue
        game_date = fn[:-len('.jsonl')]
        keys = []
        try:
            with open(os.path.join(PREDICTIONS_DIR, fn)) as f:
                for line in f:
                    if not line.strip():
                        continue
                    try:
                        rec = json.loads(line)
                    except Exception:
                        continue
                    keys.append((normalize_name(rec.get('name', '')), rec.get('team'), rec.get('opponent')))
        except Exception:
            pass
        dupes[game_date] = len(keys) - len(set(keys))
    return dupes


def _prediction_source_jsonl_duplicate_counts_by_date():
    dupes = {}
    files = _prediction_jsonl_files_by_date(PREDICTIONS_ARCHIVE_DIR)
    files.update(_prediction_jsonl_files_by_date(PREDICTIONS_DIR))
    for game_date, path in sorted(files.items()):
        keys = []
        try:
            with open(path) as f:
                for line in f:
                    if not line.strip():
                        continue
                    try:
                        rec = json.loads(line)
                    except Exception:
                        continue
                    keys.append((normalize_name(rec.get('name', '')), rec.get('team'), rec.get('opponent')))
        except Exception:
            pass
        dupes[game_date] = len(keys) - len(set(keys))
    return dupes


def _prediction_parquet_duplicate_counts_by_date():
    dupes = {}
    pred_dir = wh_path('predictions')
    if not os.path.isdir(pred_dir):
        return dupes
    for fn in sorted(os.listdir(pred_dir)):
        if not fn.endswith('.parquet'):
            continue
        game_date = fn[:-len('.parquet')]
        try:
            df = wh_read_parquet('predictions', fn)
            if {'pitcher_name', 'team', 'opponent'}.issubset(df.columns):
                keys = df[['pitcher_name', 'team', 'opponent']].copy()
                keys['pitcher_name'] = keys['pitcher_name'].map(lambda v: normalize_name(v or ''))
                dupes[game_date] = int(keys.duplicated().sum())
            else:
                dupes[game_date] = 0
        except Exception:
            dupes[game_date] = 0
    return dupes


def _outcome_jsonl_counts_by_date():
    counts = {}
    if not os.path.exists(OUTCOMES_LOG):
        return counts
    try:
        with open(OUTCOMES_LOG) as f:
            for line in f:
                if not line.strip():
                    continue
                try:
                    rec = json.loads(line)
                except Exception:
                    continue
                game_date = rec.get('date')
                if game_date:
                    counts[game_date] = counts.get(game_date, 0) + 1
    except Exception:
        pass
    return counts


def _outcome_parquet_counts_by_date():
    counts = {}
    outcome_dir = wh_path('outcomes')
    if not os.path.isdir(outcome_dir):
        return counts
    for fn in sorted(os.listdir(outcome_dir)):
        if not fn.endswith('.parquet'):
            continue
        game_date = fn[:-len('.parquet')]
        try:
            df = wh_read_parquet('outcomes', fn)
            counts[game_date] = len(df)
        except Exception:
            counts[game_date] = 0
    return counts


def _outcome_jsonl_duplicate_counts_by_date():
    keys_by_date = {}
    if not os.path.exists(OUTCOMES_LOG):
        return {}
    try:
        with open(OUTCOMES_LOG) as f:
            for line in f:
                if not line.strip():
                    continue
                try:
                    rec = json.loads(line)
                except Exception:
                    continue
                game_date = rec.get('date')
                if not game_date:
                    continue
                keys_by_date.setdefault(game_date, []).append(
                    (normalize_name(rec.get('name', '')), rec.get('team'), rec.get('opponent'))
                )
    except Exception:
        pass
    return {d: len(keys) - len(set(keys)) for d, keys in keys_by_date.items()}


def _outcome_parquet_duplicate_counts_by_date():
    dupes = {}
    outcome_dir = wh_path('outcomes')
    if not os.path.isdir(outcome_dir):
        return dupes
    for fn in sorted(os.listdir(outcome_dir)):
        if not fn.endswith('.parquet'):
            continue
        game_date = fn[:-len('.parquet')]
        try:
            df = wh_read_parquet('outcomes', fn)
            if {'pitcher_name', 'team', 'opponent'}.issubset(df.columns):
                keys = df[['pitcher_name', 'team', 'opponent']].copy()
                keys['pitcher_name'] = keys['pitcher_name'].map(lambda v: normalize_name(v or ''))
                dupes[game_date] = int(keys.duplicated().sum())
            else:
                dupes[game_date] = 0
        except Exception:
            dupes[game_date] = 0
    return dupes


OUTCOME_DUPLICATE_KEY_FIELDS = (
    'date',
    'normalized_pitcher_name',
    'team',
    'opponent',
    'home_away',
    'game_id_or_game_pk',
    'actual_line_fingerprint',
    'no_start',
)


def _outcome_actual_line_fingerprint(record):
    actual_line = record.get('actual_line')
    if isinstance(actual_line, dict) and actual_line:
        return json.dumps(actual_line, sort_keys=True, separators=(',', ':'), default=str)
    return json.dumps({
        'actual_pts': record.get('actual_pts'),
        'no_start': bool(record.get('no_start')),
    }, sort_keys=True, separators=(',', ':'), default=str)


def _outcome_stable_duplicate_key(record):
    return (
        record.get('date') or record.get('game_date'),
        normalize_name(record.get('name') or record.get('pitcher_name') or ''),
        record.get('team'),
        record.get('opponent'),
        record.get('home_away'),
        record.get('game_id') or record.get('game_pk'),
        _outcome_actual_line_fingerprint(record),
        bool(record.get('no_start')),
    )


def _outcome_exact_duplicate_key(record):
    return json.dumps(record, sort_keys=True, separators=(',', ':'), ensure_ascii=False, default=str)


def _read_outcome_log_records():
    records = []
    if not os.path.exists(OUTCOMES_LOG):
        return records
    with open(OUTCOMES_LOG) as f:
        for line_no, line in enumerate(f, 1):
            if not line.strip():
                continue
            try:
                records.append((line_no, json.loads(line)))
            except Exception:
                continue
    return records


def analyze_outcome_duplicates():
    records = _read_outcome_log_records()
    stable = {}
    exact = {}
    for line_no, rec in records:
        stable.setdefault(_outcome_stable_duplicate_key(rec), []).append((line_no, rec))
        exact.setdefault(_outcome_exact_duplicate_key(rec), []).append(line_no)
    stable_groups = [items for items in stable.values() if len(items) > 1]
    exact_groups = [lines for lines in exact.values() if len(lines) > 1]
    by_date = {}
    for items in stable_groups:
        game_date = items[0][1].get('date') or items[0][1].get('game_date') or 'unknown'
        by_date[game_date] = by_date.get(game_date, 0) + len(items) - 1
    return {
        'total_rows': len(records),
        'stable_groups': stable_groups,
        'stable_duplicate_rows': sum(len(items) - 1 for items in stable_groups),
        'exact_groups': exact_groups,
        'exact_duplicate_rows': sum(len(lines) - 1 for lines in exact_groups),
        'by_date': by_date,
    }


def audit_outcome_duplicates():
    """Dry-run audit for duplicate joined outcome rows."""
    stats = analyze_outcome_duplicates()
    _, learning_stats = _load_outcomes_from_jsonl_for_learning(return_stats=True)
    print("OUTCOME DUPLICATE AUDIT")
    print("=" * 60)
    print(f"Source: {OUTCOMES_LOG}")
    print(f"Total JSONL outcome rows: {stats['total_rows']}")
    print("Duplicate key:")
    print("  " + ", ".join(OUTCOME_DUPLICATE_KEY_FIELDS))
    print("\nPlain-language meaning:")
    print("  Rows are treated as duplicate candidates when they describe the same")
    print("  pitcher start: same date, normalized pitcher, team, opponent, home/away,")
    print("  game id when present, actual line fingerprint, and no-start status.")
    print("  The audit is dry-run only and does not modify predictions_outcomes.jsonl.")

    print("\nDuplicate summary")
    print(f"  Stable duplicate groups: {len(stats['stable_groups'])}")
    print(f"  Stable duplicate rows beyond first occurrence: {stats['stable_duplicate_rows']}")
    print(f"  Exact duplicate groups: {len(stats['exact_groups'])}")
    print(f"  Exact duplicate rows beyond first occurrence: {stats['exact_duplicate_rows']}")

    print("\nLearned-bias read-time sample selection")
    print(f"  Raw outcome rows: {learning_stats['raw_rows']}")
    print(f"  Exact duplicates removed for learning: {learning_stats['exact_duplicates_removed']}")
    print(f"  Rows excluded before learning (no-start or no residual): {learning_stats['rows_excluded_before_learning']}")
    print(f"  Rows eligible after exact dedupe: {learning_stats['eligible_rows_after_exact_dedupe']}")
    print(f"  Unique actual starts used for learning: {learning_stats['unique_actual_starts']}")
    print(f"  Snapshot groups collapsed for learning: {learning_stats['snapshot_groups_collapsed']}")
    print(f"  Snapshot rows collapsed for learning: {learning_stats['snapshot_rows_removed']}")

    print("\nDuplicate rows by date")
    if stats['by_date']:
        for game_date in sorted(stats['by_date']):
            print(f"  {game_date}: {stats['by_date'][game_date]} duplicate row(s)")
    else:
        print("  None detected")

    print("\nSample duplicate groups")
    if stats['stable_groups']:
        for items in stats['stable_groups'][:8]:
            first = items[0][1]
            line_nums = ', '.join(str(line_no) for line_no, _ in items[:8])
            print(
                f"  {first.get('date')} | {first.get('name')} | "
                f"{first.get('team')} vs {first.get('opponent')} "
                f"({first.get('home_away') or '?'}) | lines {line_nums}"
            )
    else:
        print("  None")

    print("\nNo data was modified.")
    if stats['stable_duplicate_rows']:
        print("Learning now uses read-time sample selection, so dedupe is not required for learned-bias safety.")
        print("Run --dedupe-outcomes only if you intentionally want to rewrite snapshot-preserving history.")
    return stats


def dedupe_outcomes():
    """Rewrite predictions_outcomes.jsonl after backing it up, keeping first stable key."""
    stats = analyze_outcome_duplicates()
    if not os.path.exists(OUTCOMES_LOG):
        print(f"No outcomes log found: {OUTCOMES_LOG}")
        return stats
    if not stats['stable_duplicate_rows']:
        print("No stable duplicate outcome rows detected; nothing to dedupe.")
        return stats

    print("WARNING: --dedupe-outcomes rewrites predictions_outcomes.jsonl and collapses")
    print("stable duplicate actual-start rows. Learned-bias training does not require")
    print("this repair because it now dedupes/selects samples at read time.")

    records = _read_outcome_log_records()
    seen = set()
    kept = []
    for _, rec in records:
        key = _outcome_stable_duplicate_key(rec)
        if key in seen:
            continue
        seen.add(key)
        kept.append(rec)

    import shutil
    backup = f"{OUTCOMES_LOG}.bak-{datetime.now().strftime('%Y%m%d-%H%M%S')}"
    shutil.copy2(OUTCOMES_LOG, backup)
    tmp_path = f"{OUTCOMES_LOG}.tmp"
    with open(tmp_path, 'w') as f:
        for rec in kept:
            f.write(json.dumps(rec, sort_keys=True) + '\n')
    os.replace(tmp_path, OUTCOMES_LOG)

    print("Outcome duplicate repair complete")
    print(f"  Backup: {backup}")
    print(f"  Before rows: {stats['total_rows']}")
    print(f"  After rows: {len(kept)}")
    print(f"  Removed rows: {stats['total_rows'] - len(kept)}")
    if _warehouse_parquet_files('outcomes'):
        print("Warehouse outcome Parquet files exist.")
        print("Rerun: python3.11 -B engine/fantasy_tracker.py --backfill-warehouse-outcomes")
    return stats


def _sp_start_feature_files():
    feature_dir = wh_path('features', 'sp_start_features')
    if not os.path.isdir(feature_dir):
        return []
    return [
        os.path.join(feature_dir, fn)
        for fn in sorted(os.listdir(feature_dir))
        if fn.endswith('.parquet')
    ]


def _sp_start_feature_counts_by_date():
    counts = {}
    for path in _sp_start_feature_files():
        game_date = os.path.basename(path)[:-len('.parquet')]
        try:
            df = pd.read_parquet(path)
            counts[game_date] = len(df)
        except Exception:
            counts[game_date] = 0
    return counts


def _sp_start_feature_duplicate_counts_by_date():
    dupes = {}
    for path in _sp_start_feature_files():
        game_date = os.path.basename(path)[:-len('.parquet')]
        try:
            df = pd.read_parquet(path)
            if {'start_id', 'snapshot_time'}.issubset(df.columns):
                dupes[game_date] = int(df[['start_id', 'snapshot_time']].duplicated().sum())
            else:
                dupes[game_date] = len(df)
        except Exception:
            dupes[game_date] = 0
    return dupes


def _sp_start_feature_columns():
    cols = set()
    for path in _sp_start_feature_files():
        try:
            cols.update(pd.read_parquet(path).columns)
        except Exception:
            continue
    return sorted(cols)


def _duplicate_style_feature_columns(columns):
    cols = set(columns or [])
    pairs = []
    for col in cols:
        if not col.startswith('feature_'):
            continue
        plain = col[len('feature_'):]
        if plain in cols:
            pairs.append((plain, col))
    return sorted(pairs)


def _sp_start_feature_leakage_columns(columns):
    leakage = []
    exact = SP_START_EXCLUDED_LABEL_COLUMNS | {
        'actual_ip', 'actual_k', 'actual_er', 'actual_win',
        'residual', 'residual_raw',
    }
    for col in columns:
        c = col.lower()
        if c in exact or c.startswith('actual_') or 'residual' in c:
            leakage.append(col)
    return sorted(set(leakage))


def _sp_start_feature_null_heavy():
    frames = []
    for path in _sp_start_feature_files():
        try:
            frames.append(pd.read_parquet(path))
        except Exception:
            continue
    if not frames:
        return []
    df = pd.concat(frames, ignore_index=True, sort=False)
    total = len(df)
    if total == 0:
        return []
    out = []
    for col in sorted(df.columns):
        n_null = int(df[col].isna().sum())
        if n_null / total >= 0.70:
            out.append((col, n_null, total, round(100 * n_null / total)))
    return out


def _sp_start_feature_weather_coverage():
    frames = []
    for path in _sp_start_feature_files():
        try:
            frames.append(pd.read_parquet(path, columns=None))
        except Exception:
            continue
    if not frames:
        return []
    df = pd.concat(frames, ignore_index=True, sort=False)
    total = len(df)
    if total == 0:
        return []
    out = []
    for col in WEATHER_VENUE_FEATURES:
        if col in df.columns:
            populated = int(df[col].notna().sum())
        else:
            populated = 0
        out.append((col, populated, total, round(100 * populated / total)))
    return out


def _sp_start_feature_workload_coverage():
    frames = []
    for path in _sp_start_feature_files():
        try:
            frames.append(pd.read_parquet(path, columns=None))
        except Exception:
            continue
    if not frames:
        return []
    df = pd.concat(frames, ignore_index=True, sort=False)
    total = len(df)
    if total == 0:
        return []
    out = []
    for col in WORKLOAD_FEATURES:
        if col in df.columns:
            populated = int(df[col].notna().sum())
        else:
            populated = 0
        out.append((col, populated, total, round(100 * populated / total)))
    return out


def _training_sp_starts_stats():
    stats = {
        'rows': 0,
        'rows_with_labels': 0,
        'rows_without_labels': 0,
        'duplicate_join_keys': 0,
        'join_key_audit': 'none available',
        'possible_leakage_columns': [],
    }
    conn = None
    try:
        conn = wh_conn()
        cols = _table_columns(conn, 'training_sp_starts')
        if not cols:
            return stats
        stats['rows'] = int(conn.execute("SELECT COUNT(*) FROM training_sp_starts").fetchone()[0] or 0)
        if 'has_label' in cols:
            stats['rows_with_labels'] = int(conn.execute(
                "SELECT COUNT(*) FROM training_sp_starts WHERE COALESCE(has_label, FALSE)"
            ).fetchone()[0] or 0)
        elif 'actual_pts' in cols:
            stats['rows_with_labels'] = int(conn.execute(
                "SELECT COUNT(*) FROM training_sp_starts WHERE actual_pts IS NOT NULL"
            ).fetchone()[0] or 0)
        stats['rows_without_labels'] = max(0, stats['rows'] - stats['rows_with_labels'])

        if {'start_id', 'snapshot_time'}.issubset(cols):
            stats['join_key_audit'] = 'start_id + snapshot_time'
            stats['duplicate_join_keys'] = int(conn.execute("""
                SELECT COALESCE(SUM(cnt - 1), 0)
                FROM (
                  SELECT start_id, snapshot_time, COUNT(*) AS cnt
                  FROM training_sp_starts
                  GROUP BY start_id, snapshot_time
                  HAVING COUNT(*) > 1
                )
            """).fetchone()[0] or 0)
        elif {'game_date', 'snapshot_time', 'pitcher_name', 'team', 'opponent'}.issubset(cols):
            stats['join_key_audit'] = 'game_date + snapshot_time + pitcher_name + team + opponent'
            stats['duplicate_join_keys'] = int(conn.execute("""
                SELECT COALESCE(SUM(cnt - 1), 0)
                FROM (
                  SELECT game_date, snapshot_time, pitcher_name, team, opponent, COUNT(*) AS cnt
                  FROM training_sp_starts
                  GROUP BY game_date, snapshot_time, pitcher_name, team, opponent
                  HAVING COUNT(*) > 1
                )
            """).fetchone()[0] or 0)

        allowed_labels = TRAINING_LABEL_COLUMNS | {'has_label'}
        leakage_exact = {'actual_line', 'actual_decision', 'residual_raw', 'no_start'}
        leakage = []
        for col in cols:
            c = col.lower()
            if c in allowed_labels:
                continue
            if c in leakage_exact or c.startswith('actual_') or 'residual' in c:
                leakage.append(col)
        stats['possible_leakage_columns'] = sorted(set(leakage))
        return stats
    except Exception as e:
        stats['join_key_audit'] = f'audit failed: {type(e).__name__}: {e}'
        return stats
    finally:
        if conn is not None:
            try:
                conn.close()
            except Exception:
                pass


FEATURE_ERROR_EXCLUDED_COLUMNS = {
    'actual_pts', 'actual_ip', 'actual_k', 'actual_er', 'actual_bb',
    'actual_h', 'actual_hits', 'actual_hr', 'actual_win', 'actual_decision',
    'actual_line', 'residual', 'residual_raw', 'no_start', 'has_label',
    'start_id', 'game_id', 'game_pk', 'game_date', 'snapshot_time',
    'logged_at', 'pitcher_name', 'pitcher_id', 'team', 'opponent',
    'home_away', 'status', 'lineup_status', 'probable_status',
    'learned_adjustments',
}


def _is_numeric_series(series):
    try:
        return pd.api.types.is_numeric_dtype(series)
    except Exception:
        return False


def analyze_feature_errors(min_bucket_n=12, max_features=25):
    """Read-only exploratory error analysis over warehouse training rows."""
    print("WAREHOUSE FEATURE ERROR ANALYSIS")
    print("=" * 60)
    print("Analysis only: these findings are not automatically applied to predictions.")

    try:
        conn = wh_conn()
        cols = _table_columns(conn, 'training_sp_starts')
        if not cols:
            print("No warehouse training view is available yet.")
            conn.close()
            return {'labeled_rows': 0, 'features_analyzed': 0, 'findings': []}
        df = conn.execute(
            "SELECT * FROM training_sp_starts WHERE COALESCE(has_label, FALSE)"
        ).fetchdf()
        feature_dates = conn.execute(
            "SELECT MIN(game_date), MAX(game_date), COUNT(*) FROM training_sp_starts"
        ).fetchone()
        outcome_dates = (None, None)
        if 'warehouse_outcomes' in {
                row[0] for row in conn.execute(
                    "SELECT table_name FROM information_schema.tables WHERE table_type = 'VIEW'"
                ).fetchall()
        }:
            outcome_dates = conn.execute(
                "SELECT MIN(game_date), MAX(game_date) FROM warehouse_outcomes"
            ).fetchone()
        conn.close()
    except Exception as e:
        print(f"Feature error analysis unavailable: {type(e).__name__}: {e}")
        return {'labeled_rows': 0, 'features_analyzed': 0, 'findings': []}

    if df.empty:
        print("No labeled training rows yet. Feature rows are currently after the latest outcome date.")
        if feature_dates and feature_dates[2]:
            print(f"  Feature date range: {feature_dates[0]} through {feature_dates[1]}")
        if outcome_dates and outcome_dates[0]:
            print(f"  Latest outcome date: {outcome_dates[1]}")
        return {'labeled_rows': 0, 'features_analyzed': 0, 'findings': []}

    if 'actual_pts' not in df.columns or df['actual_pts'].isna().all():
        print("No usable actual_pts labels found in training_sp_starts.")
        return {'labeled_rows': len(df), 'features_analyzed': 0, 'findings': []}

    if 'predicted_pts' in df.columns and not df['predicted_pts'].isna().all():
        df['_analysis_predicted_pts'] = pd.to_numeric(df['predicted_pts'], errors='coerce')
    elif 'residual' in df.columns:
        actual = pd.to_numeric(df['actual_pts'], errors='coerce')
        residual = pd.to_numeric(df['residual'], errors='coerce')
        df['_analysis_predicted_pts'] = actual - residual
    else:
        print("No prediction-point column or residual is available for analysis.")
        return {'labeled_rows': len(df), 'features_analyzed': 0, 'findings': []}

    df['_analysis_actual_pts'] = pd.to_numeric(df['actual_pts'], errors='coerce')
    df['_analysis_residual'] = df['_analysis_actual_pts'] - df['_analysis_predicted_pts']
    df['_analysis_abs_error'] = df['_analysis_residual'].abs()
    df = df.dropna(subset=['_analysis_predicted_pts', '_analysis_actual_pts', '_analysis_residual'])
    if df.empty:
        print("No rows have both predicted and actual points available for analysis.")
        return {'labeled_rows': 0, 'features_analyzed': 0, 'findings': []}

    excluded = set(FEATURE_ERROR_EXCLUDED_COLUMNS) | {
        '_analysis_predicted_pts', '_analysis_actual_pts',
        '_analysis_residual', '_analysis_abs_error',
    }
    feature_cols = []
    for col in df.columns:
        c = col.lower()
        if col in excluded or c in excluded:
            continue
        if c.startswith('actual_') or 'residual' in c:
            continue
        if not _is_numeric_series(df[col]):
            continue
        if df[col].notna().sum() >= min_bucket_n * 2:
            feature_cols.append(col)

    findings = []
    features_analyzed = 0
    for col in sorted(feature_cols):
        work = df[[col, '_analysis_predicted_pts', '_analysis_actual_pts', '_analysis_residual', '_analysis_abs_error']].dropna()
        if len(work) < min_bucket_n * 2:
            continue
        unique_vals = work[col].nunique(dropna=True)
        if unique_vals < 2:
            continue
        q = min(4, max(2, len(work) // min_bucket_n))
        q = min(q, unique_vals)
        try:
            work['_bucket'] = pd.qcut(work[col], q=q, duplicates='drop')
        except Exception:
            continue
        if work['_bucket'].nunique(dropna=True) < 2:
            continue
        features_analyzed += 1
        for bucket, bucket_df in work.groupby('_bucket', observed=True):
            n = len(bucket_df)
            if n < min_bucket_n:
                continue
            mean_residual = float(bucket_df['_analysis_residual'].mean())
            findings.append({
                'feature': col,
                'bucket': str(bucket),
                'n': int(n),
                'mean_predicted': float(bucket_df['_analysis_predicted_pts'].mean()),
                'mean_actual': float(bucket_df['_analysis_actual_pts'].mean()),
                'mean_residual': mean_residual,
                'mae': float(bucket_df['_analysis_abs_error'].mean()),
            })

    findings.sort(key=lambda row: (-abs(row['mean_residual']), row['feature'], row['bucket']))
    print(f"\nLabeled training rows analyzed: {len(df)}")
    print(f"Numeric features analyzed: {features_analyzed}")
    print(f"Minimum bucket sample size: {min_bucket_n}")
    if not findings:
        print("\nNo reliable feature buckets met the sample-size threshold yet.")
        return {'labeled_rows': len(df), 'features_analyzed': features_analyzed, 'findings': []}

    print("\nTop exploratory feature-error buckets")
    print(f"{'Feature':<28s} {'Bucket/range':<28s} {'n':>4s} {'Pred':>7s} {'Actual':>7s} {'Resid':>7s} {'MAE':>7s}")
    print("-" * 96)
    for row in findings[:max_features]:
        print(
            f"{row['feature'][:28]:<28s} {row['bucket'][:28]:<28s} "
            f"{row['n']:>4d} {row['mean_predicted']:>7.2f} "
            f"{row['mean_actual']:>7.2f} {row['mean_residual']:>+7.2f} {row['mae']:>7.2f}"
        )
    print("\nExploratory only: use this to inspect error patterns; it does not change scoring or learned corrections.")
    return {'labeled_rows': len(df), 'features_analyzed': features_analyzed, 'findings': findings}


MODEL_BASELINE_SPECS = [
    ('Current predicted points', ['predicted_pts', 'final_pts']),
    ('Raw predicted points before learned corrections', ['predicted_pts_raw', 'pts_pre_adj']),
    ('Base projection points', ['base_projection_pts', 'projection_pts', 'proj_pts']),
    ('Projection plus matchup/park', ['base_pts', 'matchup_pts', 'adjusted_pts']),
]


def analyze_model_baselines():
    """Read-only comparison of current predictions against available baselines."""
    print("WAREHOUSE MODEL BASELINE COMPARISON")
    print("=" * 60)
    print("Analysis only: these comparisons are not automatically applied to predictions.")

    prediction_files = _warehouse_parquet_files('predictions')
    if not prediction_files:
        print("No warehouse prediction Parquet files found. Run --backfill-warehouse-features-from-archive first.")
        return {'labeled_rows': 0, 'baselines': []}

    conn = None
    try:
        conn = wh_conn()
        train_cols = _table_columns(conn, 'training_sp_starts')
        labeled_rows = int(conn.execute(
            "SELECT COUNT(*) FROM training_sp_starts WHERE COALESCE(has_label, FALSE)"
        ).fetchone()[0] or 0)
        if labeled_rows == 0:
            print("No labeled training rows yet. Feature rows are currently after the latest outcome date.")
            return {'labeled_rows': 0, 'baselines': []}

        pred_glob = _sql_path(os.path.join(wh_path('predictions'), '*.parquet'))
        conn.execute(
            "CREATE OR REPLACE TEMP VIEW warehouse_predictions_all AS "
            f"SELECT * FROM read_parquet('{pred_glob}', union_by_name=true)"
        )
        pred_cols = _table_columns(conn, 'warehouse_predictions_all')
        candidate_cols = sorted({col for _, cols in MODEL_BASELINE_SPECS for col in cols})
        select_parts = [
            't."start_id" AS "start_id"',
            't."snapshot_time" AS "snapshot_time"',
            't."game_date" AS "game_date"',
            't."pitcher_name" AS "pitcher_name"',
            'try_cast(t."actual_pts" AS DOUBLE) AS "actual_pts"',
        ]
        for col in candidate_cols:
            if col in train_cols:
                select_parts.append(f'try_cast(t."{col}" AS DOUBLE) AS "train__{col}"')
            if col in pred_cols:
                select_parts.append(f'try_cast(p."{col}" AS DOUBLE) AS "pred__{col}"')
        select_sql = ',\n              '.join(select_parts)
        join_sql = (
            "t.start_id = p.start_id "
            "AND coalesce(t.snapshot_time, '') = coalesce(p.snapshot_time, p.logged_at, '')"
        )
        df = conn.execute(f"""
            SELECT
              {select_sql}
            FROM training_sp_starts t
            LEFT JOIN warehouse_predictions_all p
              ON {join_sql}
            WHERE COALESCE(t.has_label, FALSE)
        """).fetchdf()
    except Exception as e:
        print(f"Model baseline analysis unavailable: {type(e).__name__}: {e}")
        return {'labeled_rows': 0, 'baselines': []}
    finally:
        if conn is not None:
            try:
                conn.close()
            except Exception:
                pass

    if df.empty or 'actual_pts' not in df.columns:
        print("No labeled rows with actual points are available for baseline analysis.")
        return {'labeled_rows': 0, 'baselines': []}

    df['actual_pts'] = pd.to_numeric(df['actual_pts'], errors='coerce')
    df = df.dropna(subset=['actual_pts'])
    if df.empty:
        print("No labeled rows with numeric actual points are available for baseline analysis.")
        return {'labeled_rows': 0, 'baselines': []}

    results = []
    skipped = []
    for label, candidates in MODEL_BASELINE_SPECS:
        chosen = None
        source_col = None
        for col in candidates:
            for prefixed in (f'pred__{col}', f'train__{col}'):
                if prefixed in df.columns and pd.to_numeric(df[prefixed], errors='coerce').notna().any():
                    chosen = pd.to_numeric(df[prefixed], errors='coerce')
                    source_col = prefixed
                    break
            if chosen is not None:
                break
        if chosen is None:
            skipped.append({
                'label': label,
                'reason': f"no populated column found ({', '.join(candidates)})",
            })
            continue
        work = pd.DataFrame({
            'predicted': chosen,
            'actual': df['actual_pts'],
        }).dropna()
        if work.empty:
            skipped.append({
                'label': label,
                'reason': f"columns were present but had no labeled rows ({', '.join(candidates)})",
            })
            continue
        residual = work['actual'] - work['predicted']
        abs_err = residual.abs()
        rmse = math.sqrt(float((residual ** 2).mean()))
        results.append({
            'label': label,
            'source_col': source_col,
            'n': int(len(work)),
            'mae': float(abs_err.mean()),
            'rmse': rmse,
            'bias': float(residual.mean()),
            'mean_predicted': float(work['predicted'].mean()),
            'mean_actual': float(work['actual'].mean()),
        })

    print(f"\nLabeled rows available: {len(df)}")
    if len(df) < 100:
        print(
            "Small-sample warning: fewer than 100 labeled rows are available, "
            "so treat these rankings as directional rather than conclusive."
        )
    if skipped:
        print("\nSkipped unavailable baselines")
        for item in skipped:
            print(f"  - {item['label']}: {item['reason']}")

    if not results:
        print("\nNo populated prediction/baseline columns were available to compare.")
        return {'labeled_rows': len(df), 'baselines': []}

    results.sort(key=lambda row: (row['mae'], row['rmse']))
    print("\nBaseline comparison, sorted by MAE")
    print(
        f"{'Baseline name':<44s} {'Source column':<24s} {'n':>4s} "
        f"{'MAE':>7s} {'RMSE':>7s} {'Bias':>7s} {'Mean pred':>9s} {'Mean actual':>11s}"
    )
    print("-" * 126)
    for row in results:
        print(
            f"{row['label'][:44]:<44s} {row['source_col'][:24]:<24s} "
            f"{row['n']:>4d} {row['mae']:>7.2f} {row['rmse']:>7.2f} "
            f"{row['bias']:>+7.2f} {row['mean_predicted']:>9.2f} {row['mean_actual']:>11.2f}"
        )
    best = results[0]
    current = next((row for row in results if row['label'] == 'Current predicted points'), None)
    simpler = [row for row in results if row['label'] != 'Current predicted points']
    better_simpler = [row for row in simpler if current and row['mae'] < current['mae']]
    print("\nInterpretation")
    print(f"  Best baseline by MAE: {best['label']} ({best['mae']:.2f} MAE).")
    if current and not better_simpler:
        print("  Current predicted points beat or tied the simpler available baselines by MAE.")
    elif current and better_simpler:
        names = ', '.join(f"{row['label']} ({row['mae']:.2f})" for row in better_simpler)
        print(f"  Current predicted points did not beat these simpler baselines by MAE: {names}.")
    else:
        print("  Current predicted points were unavailable, so no current-vs-baseline comparison was possible.")
    print("Analysis only: this does not change scoring, prediction outputs, or learned corrections.")
    return {'labeled_rows': len(df), 'baselines': results}


START_SIT_STATUS_GROUPS = {
    'MY ROSTER': 'MY ROSTER',
    'FA': 'FA/WAIVER',
    'WAIVER': 'FA/WAIVER',
}


def _start_sit_rows_from_warehouse():
    """Load labeled start/sit evaluation rows from warehouse training view."""
    conn = None
    try:
        conn = wh_conn()
        cols = _table_columns(conn, 'training_sp_starts')
        if not cols or 'actual_pts' not in cols:
            return None, 'warehouse training view unavailable'
        label_filter = "COALESCE(has_label, FALSE)" if 'has_label' in cols else "actual_pts IS NOT NULL"
        df = conn.execute(f"""
            SELECT *
            FROM training_sp_starts
            WHERE {label_filter}
              AND actual_pts IS NOT NULL
        """).fetchdf()
        if df.empty:
            return None, 'warehouse training view has no labeled rows'
        return df, 'warehouse training_sp_starts'
    except Exception as e:
        return None, f'warehouse unavailable ({type(e).__name__}: {e})'
    finally:
        if conn is not None:
            try:
                conn.close()
            except Exception:
                pass


def _start_sit_rows_from_outcome_jsonl():
    """Labeled start/sit rows from the full outcome history.

    This reuses the learned-bias sample selector so repeated prediction
    snapshots do not cause one real pitcher start to count multiple times.
    """
    raw_records = [rec for _, rec in _read_outcome_log_records()]
    records, stats = select_learning_outcome_samples(raw_records)
    records = [
        rec for rec in records
        if not rec.get('no_start') and rec.get('actual_pts') is not None
    ]
    if not records:
        return pd.DataFrame(), 'prediction/outcome JSONL selected sample'
    rows = []
    for rec in records:
        row = dict(rec)
        row['game_date'] = rec.get('date') or rec.get('game_date')
        row['pitcher_name'] = rec.get('name') or rec.get('pitcher_name')
        rows.append(row)
    source = (
        "prediction/outcome JSONL selected sample "
        f"({stats['raw_rows']} raw rows -> {stats['unique_actual_starts']} unique starts)"
    )
    return pd.DataFrame(rows), source


def _start_sit_predicted_advice(tier, predicted_pts):
    tier_norm = str(tier or '').strip().lower()
    if tier_norm in ('must_start', 'start'):
        return 'START'
    if tier_norm == 'borderline':
        return 'BORDERLINE'
    if tier_norm in ('avoid', 'sit'):
        return 'SIT'
    pts = _safe_float(predicted_pts)
    if pts is None:
        return 'UNKNOWN'
    if pts >= 10:
        return 'START'
    if pts >= 8:
        return 'BORDERLINE'
    return 'SIT'


def _start_sit_actual_band(actual_pts):
    actual = _safe_float(actual_pts)
    if actual is None:
        return 'unknown'
    if actual <= 0:
        return 'disaster_start'
    if actual < 5:
        return 'bad_start'
    if actual >= 18:
        return 'smash_start'
    if actual >= 12:
        return 'good_start'
    if actual >= 8:
        return 'usable_start'
    return 'poor_start'


def _start_sit_status_group(status):
    status_norm = str(status or '').strip().upper()
    return START_SIT_STATUS_GROUPS.get(status_norm, 'OTHER' if status_norm else 'UNKNOWN')


def _start_sit_prepare_dataframe(df):
    work = df.copy()
    if 'features' in work.columns:
        feature_cols = [
            'opp_rank', 'opp_ops', 'opp_ops_raw', 'park_factor', 'park',
            'platoon', 'trend', 'recent_era', 'proj_k9', 'k9',
            'workload_risk_score', 'pitch_matchup_score',
            'opp_il_count', 'opp_il_returns_count',
        ]
        for col in feature_cols:
            if col not in work.columns:
                work[col] = None
            for idx, features in work['features'].items():
                current = work.at[idx, col]
                if current is not None and not pd.isna(current):
                    continue
                if isinstance(features, dict) and features.get(col) is not None:
                    work.at[idx, col] = features.get(col)
    rename_map = {
        'date': 'game_date',
        'name': 'pitcher_name',
        'pts': 'predicted_pts',
    }
    for old, new in rename_map.items():
        if new not in work.columns and old in work.columns:
            work[new] = work[old]
    if 'predicted_pts' not in work.columns:
        if 'final_pts' in work.columns:
            work['predicted_pts'] = work['final_pts']
        elif 'base_pts' in work.columns:
            work['predicted_pts'] = work['base_pts']
    required_defaults = {
        'game_date': None,
        'pitcher_name': None,
        'team': None,
        'opponent': None,
        'home_away': None,
        'status': None,
        'tier': None,
        'predicted_pts': None,
    }
    for col, default in required_defaults.items():
        if col not in work.columns:
            work[col] = default
    work['actual_pts'] = pd.to_numeric(work['actual_pts'], errors='coerce')
    work['predicted_pts'] = pd.to_numeric(work['predicted_pts'], errors='coerce')
    work = work.dropna(subset=['actual_pts'])
    if 'no_start' in work.columns:
        work = work[work['no_start'] != True]  # noqa: E712
    work['predicted_advice'] = [
        _start_sit_predicted_advice(tier, pts)
        for tier, pts in zip(work['tier'], work['predicted_pts'])
    ]
    work['actual_band'] = [_start_sit_actual_band(v) for v in work['actual_pts']]
    work['status_group'] = [_start_sit_status_group(v) for v in work['status']]
    work['tier_group'] = [
        'avoid/sit' if str(v or '').strip().lower() in ('avoid', 'sit') else str(v or 'unknown').strip().lower()
        for v in work['tier']
    ]
    return work


def _start_sit_rate(numerator, denominator):
    return (100.0 * numerator / denominator) if denominator else 0.0


def _start_sit_metric_summary(df):
    total = len(df)
    start = df[df['predicted_advice'] == 'START']
    borderline = df[df['predicted_advice'] == 'BORDERLINE']
    sit = df[df['predicted_advice'] == 'SIT']
    disasters = df[df['actual_pts'] <= 0]
    return {
        'total': total,
        'start_count': len(start),
        'borderline_count': len(borderline),
        'sit_count': len(sit),
        'start_hit_rate': _start_sit_rate(int((start['actual_pts'] >= 8).sum()), len(start)),
        'start_good_rate': _start_sit_rate(int((start['actual_pts'] >= 12).sum()), len(start)),
        'start_bust_rate': _start_sit_rate(int((start['actual_pts'] < 5).sum()), len(start)),
        'sit_correct_avoid_rate': _start_sit_rate(int((sit['actual_pts'] < 8).sum()), len(sit)),
        'sit_missed_opportunity_rate': _start_sit_rate(int((sit['actual_pts'] >= 12).sum()), len(sit)),
        'borderline_usable_rate': _start_sit_rate(int((borderline['actual_pts'] >= 8).sum()), len(borderline)),
        'disaster_sit': int((disasters['predicted_advice'] == 'SIT').sum()),
        'disaster_borderline': int((disasters['predicted_advice'] == 'BORDERLINE').sum()),
        'disaster_start': int((disasters['predicted_advice'] == 'START').sum()),
    }


def _print_start_sit_metric_block(title, df):
    metrics = _start_sit_metric_summary(df)
    print(f"\n{title}")
    print(f"  total labeled starts: {metrics['total']}")
    print(
        f"  predicted START / BORDERLINE / SIT: "
        f"{metrics['start_count']} / {metrics['borderline_count']} / {metrics['sit_count']}"
    )
    print(f"  START hit rate (actual >= 8): {metrics['start_hit_rate']:.1f}%")
    print(f"  START good rate (actual >= 12): {metrics['start_good_rate']:.1f}%")
    print(f"  START bust rate (actual < 5): {metrics['start_bust_rate']:.1f}%")
    print(f"  SIT correct avoid rate (actual < 8): {metrics['sit_correct_avoid_rate']:.1f}%")
    print(f"  SIT missed opportunity rate (actual >= 12): {metrics['sit_missed_opportunity_rate']:.1f}%")
    print(f"  BORDERLINE usable rate (actual >= 8): {metrics['borderline_usable_rate']:.1f}%")
    print(
        "  disaster starts (actual <= 0) predicted "
        f"SIT/BORDERLINE/START: {metrics['disaster_sit']}/"
        f"{metrics['disaster_borderline']}/{metrics['disaster_start']}"
    )
    return metrics


def _start_sit_example_line(row):
    matchup = f"{row.get('home_away') or '?'} {row.get('opponent') or '?'}"
    pred = row.get('predicted_pts')
    pred_text = f"{float(pred):.1f}" if pd.notna(pred) else "--"
    return (
        f"{row.get('game_date') or '?'} | {row.get('pitcher_name') or '?'} "
        f"({row.get('team') or '?'}, {matchup}) | tier={row.get('tier') or '?'} "
        f"| pred={pred_text} | actual={float(row.get('actual_pts')):.1f} "
        f"| status={row.get('status') or '?'}"
    )


def _print_start_sit_examples(title, rows):
    print(f"\n{title}")
    if rows.empty:
        print("  None")
        return
    for _, row in rows.head(5).iterrows():
        print(f"  - {_start_sit_example_line(row)}")


def _load_start_sit_analysis_rows():
    """Load the labeled rows used by start/sit decision analysis."""
    warehouse_df, warehouse_source = _start_sit_rows_from_warehouse()
    outcome_df, outcome_source = _start_sit_rows_from_outcome_jsonl()

    prepared = []
    for df, source in ((warehouse_df, warehouse_source), (outcome_df, outcome_source)):
        if df is None or df.empty:
            continue
        work = _start_sit_prepare_dataframe(df)
        work = work[work['predicted_advice'] != 'UNKNOWN']
        if not work.empty:
            prepared.append((work, source))

    if not prepared:
        return pd.DataFrame(), outcome_source or warehouse_source or 'none', warehouse_source

    prepared.sort(key=lambda item: len(item[0]), reverse=True)
    work, source = prepared[0]
    skipped_source = None
    if len(prepared) > 1:
        skipped_source = f"{prepared[1][1]} ({len(prepared[1][0])} usable rows; smaller sample)"
    elif warehouse_df is None or getattr(warehouse_df, 'empty', True):
        skipped_source = warehouse_source
    return work, source, skipped_source


def analyze_start_sit_quality():
    """Read-only evaluation of fantasy start/sit decision quality."""
    print("START/SIT DECISION QUALITY ANALYSIS")
    print("=" * 60)
    print("Analysis only: this does not change scoring, predictions, tiers, or learned corrections.")

    work, source, skipped_source = _load_start_sit_analysis_rows()
    if skipped_source:
        print(f"Warehouse source skipped: {skipped_source}")
    print(f"Source: {source}")

    if work.empty:
        print("No labeled starts with actual fantasy points are available yet.")
        return {'labeled_rows': 0}

    metrics = _print_start_sit_metric_block("Overall decision quality", work)

    print("\nBy roster status")
    for status_group in ('MY ROSTER', 'FA/WAIVER', 'OTHER', 'UNKNOWN'):
        subset = work[work['status_group'] == status_group]
        if subset.empty:
            continue
        _print_start_sit_metric_block(status_group, subset)

    print("\nBy tier/confidence")
    for tier in ('must_start', 'start', 'borderline', 'avoid/sit', 'unknown'):
        subset = work[work['tier_group'] == tier]
        if subset.empty:
            continue
        _print_start_sit_metric_block(tier, subset)

    predicted_start = work[work['predicted_advice'] == 'START']
    predicted_sit = work[work['predicted_advice'] == 'SIT']
    _print_start_sit_examples(
        "Best correct starts",
        predicted_start[predicted_start['actual_pts'] >= 8].sort_values('actual_pts', ascending=False),
    )
    _print_start_sit_examples(
        "Worst recommended starts",
        predicted_start.sort_values('actual_pts', ascending=True),
    )
    _print_start_sit_examples(
        "Best avoided sits",
        predicted_sit[predicted_sit['actual_pts'] < 8].sort_values('actual_pts', ascending=True),
    )
    _print_start_sit_examples(
        "Biggest missed sits",
        predicted_sit[predicted_sit['actual_pts'] >= 12].sort_values('actual_pts', ascending=False),
    )

    print("\nInterpretation")
    if metrics['total'] < 100:
        print("  Small-sample warning: fewer than 100 labeled decisions are available.")
    if metrics['start_count'] and metrics['sit_count']:
        if metrics['start_hit_rate'] >= metrics['sit_correct_avoid_rate']:
            print("  The model currently looks stronger at identifying usable starts than avoiding traps.")
        else:
            print("  The model currently looks stronger at avoiding bad starts than identifying usable starts.")
    if metrics['borderline_count']:
        if metrics['borderline_usable_rate'] >= 60:
            print("  Borderline calls have mostly been usable so far, so they may be conservative enough.")
        elif metrics['borderline_usable_rate'] <= 40:
            print("  Borderline calls have been shaky so far and may be too aggressive.")
        else:
            print("  Borderline calls are mixed; treat them as matchup-dependent until the sample grows.")
    print("  These results are diagnostic only and are not fed back into recommendations yet.")
    return {'labeled_rows': len(work), 'metrics': metrics}


def _start_sit_signal_patterns(row):
    """Return compact pregame signal labels available on a start/sit row."""
    patterns = []
    opp_rank = _safe_float(row.get('opp_rank'))
    opp_ops = _safe_float(row.get('opp_ops') or row.get('opp_ops_raw'))
    park_factor = _safe_float(row.get('park_factor'))
    pitch_matchup_score = _safe_float(row.get('pitch_matchup_score'))
    workload_risk = _safe_float(row.get('workload_risk_score'))
    hard_hit_pct = _safe_float(row.get('hard_hit_pct'))
    xera = _safe_float(row.get('xera'))
    siera = _safe_float(row.get('siera'))
    fip = _safe_float(row.get('fip'))
    proj_era = _safe_float(row.get('proj_era'))
    proj_k9 = _safe_float(row.get('proj_k9') or row.get('k9'))
    proj_so = _safe_float(row.get('proj_so'))
    learned_adj = _safe_float(row.get('learned_adj_total') or row.get('adj_total'))
    platoon = str(row.get('platoon') or '').lower()
    trend = str(row.get('trend') or '').lower()
    status_group = row.get('status_group') or _start_sit_status_group(row.get('status'))

    if opp_rank is not None:
        if opp_rank <= 10:
            patterns.append('top-10 opponent offense')
        elif opp_rank >= 21:
            patterns.append('bottom-10 opponent offense')
    if opp_ops is not None:
        if opp_ops >= 0.740:
            patterns.append('high opponent OPS')
        elif opp_ops <= 0.690:
            patterns.append('low opponent OPS')
    if park_factor is not None:
        if park_factor >= 1.03:
            patterns.append('hitter-friendly park')
        elif park_factor <= 0.97:
            patterns.append('pitcher-friendly park')
    if platoon == 'risk':
        patterns.append('platoon risk')
    elif platoon == 'edge':
        patterns.append('platoon edge')
    if trend == 'cold':
        patterns.append('cold recent trend')
    elif trend == 'hot':
        patterns.append('hot recent trend')
    if workload_risk is not None and workload_risk >= 0.4:
        patterns.append('workload risk')
    if pitch_matchup_score is not None:
        if pitch_matchup_score <= -0.05:
            patterns.append('negative pitch-matchup score')
        elif pitch_matchup_score >= 0.05:
            patterns.append('positive pitch-matchup score')
    if hard_hit_pct is not None and hard_hit_pct >= 45:
        patterns.append('high hard-hit rate allowed')
    if xera is not None and xera >= 4.50:
        patterns.append('high xERA')
    if siera is not None and siera >= 4.50:
        patterns.append('high SIERA')
    if fip is not None and fip >= 4.50:
        patterns.append('high FIP')
    if proj_era is not None and proj_era >= 4.50:
        patterns.append('high projected ERA')
    if proj_k9 is not None:
        if proj_k9 < 7.5:
            patterns.append('low projected K/9')
        elif proj_k9 >= 9.0:
            patterns.append('high projected K/9')
    if proj_so is not None and proj_so >= 6:
        patterns.append('high projected strikeouts')
    if learned_adj is not None:
        if learned_adj >= 2.0:
            patterns.append('positive learned adjustment')
        elif learned_adj <= -2.0:
            patterns.append('negative learned adjustment')
    if status_group:
        patterns.append(f'status {status_group}')
    return patterns


def _start_sit_group_summary(df):
    if df.empty:
        return {'count': 0, 'avg_predicted': 0.0, 'avg_actual': 0.0, 'avg_residual': 0.0, 'patterns': []}
    pred = pd.to_numeric(df['predicted_pts'], errors='coerce')
    actual = pd.to_numeric(df['actual_pts'], errors='coerce')
    residual = actual - pred
    from collections import Counter
    counter = Counter()
    for _, row in df.iterrows():
        counter.update(_start_sit_signal_patterns(row))
    return {
        'count': int(len(df)),
        'avg_predicted': float(pred.mean()) if pred.notna().any() else 0.0,
        'avg_actual': float(actual.mean()) if actual.notna().any() else 0.0,
        'avg_residual': float(residual.mean()) if residual.notna().any() else 0.0,
        'patterns': counter.most_common(8),
    }


def _print_start_sit_miss_group(name, rows):
    summary = _start_sit_group_summary(rows)
    print(f"\n{name}")
    print(f"  count: {summary['count']}")
    if summary['count']:
        print(f"  average predicted points: {summary['avg_predicted']:.2f}")
        print(f"  average actual points: {summary['avg_actual']:.2f}")
        print(f"  average residual: {summary['avg_residual']:+.2f}")
        print("  common pregame patterns:")
        for label, count in summary['patterns']:
            print(f"    - {label}: {count}/{summary['count']}")
    else:
        print("  common pregame patterns: none")
    return summary


def _start_sit_signal_text(row, limit=4):
    patterns = _start_sit_signal_patterns(row)
    if not patterns:
        return 'no highlighted pregame signals'
    return '; '.join(patterns[:limit])


def _print_start_sit_miss_examples(title, rows):
    print(f"\n{title}")
    if rows.empty:
        print("  None")
        return
    for _, row in rows.head(5).iterrows():
        print(f"  - {_start_sit_example_line(row)}")
        print(f"    signals: {_start_sit_signal_text(row)}")


def analyze_start_sit_misses():
    """Read-only explanation analysis for start/sit decision misses."""
    print("START/SIT MISS EXPLANATION ANALYSIS")
    print("=" * 60)
    print("Analysis only: this does not change scoring, predictions, tiers, or learned corrections.")

    work, source, skipped_source = _load_start_sit_analysis_rows()
    if skipped_source:
        print(f"Warehouse source skipped: {skipped_source}")
    print(f"Source: {source}")
    if work.empty:
        print("No labeled starts with actual fantasy points are available yet.")
        return {'labeled_rows': 0, 'groups': {}}

    groups = {
        'start_busts': work[(work['predicted_advice'] == 'START') & (work['actual_pts'] < 5)],
        'strong_start_busts': work[
            (work['tier_group'].isin(['must_start', 'start']))
            & (work['actual_pts'] < 5)
        ],
        'missed_good_sits': work[(work['predicted_advice'] == 'SIT') & (work['actual_pts'] >= 12)],
        'missed_usable_sits': work[(work['predicted_advice'] == 'SIT') & (work['actual_pts'] >= 8)],
        'borderline_hits': work[(work['predicted_advice'] == 'BORDERLINE') & (work['actual_pts'] >= 8)],
        'borderline_busts': work[(work['predicted_advice'] == 'BORDERLINE') & (work['actual_pts'] < 5)],
    }

    print(f"\nLabeled rows analyzed: {len(work)}")
    if len(work) < 100:
        print("Small-sample warning: fewer than 100 labeled decisions are available.")

    summaries = {}
    for name, rows in groups.items():
        summaries[name] = _print_start_sit_miss_group(name, rows)

    _print_start_sit_miss_examples(
        "Top start bust examples",
        groups['start_busts'].sort_values('actual_pts', ascending=True),
    )
    _print_start_sit_miss_examples(
        "Top missed good sit examples",
        groups['missed_good_sits'].sort_values('actual_pts', ascending=False),
    )
    _print_start_sit_miss_examples(
        "Borderline hit examples",
        groups['borderline_hits'].sort_values('actual_pts', ascending=False),
    )
    _print_start_sit_miss_examples(
        "Borderline bust examples",
        groups['borderline_busts'].sort_values('actual_pts', ascending=True),
    )

    bust_patterns = summaries['start_busts']['patterns']
    missed_sit_patterns = summaries['missed_good_sits']['patterns'] or summaries['missed_usable_sits']['patterns']
    borderline_hit_rate = _start_sit_rate(len(groups['borderline_hits']), len(work[work['predicted_advice'] == 'BORDERLINE']))
    borderline_bust_rate = _start_sit_rate(len(groups['borderline_busts']), len(work[work['predicted_advice'] == 'BORDERLINE']))

    print("\nInterpretation")
    if bust_patterns:
        top = ', '.join(label for label, _ in bust_patterns[:3])
        print(f"  Start busts most often share: {top}.")
    else:
        print("  There are no start busts in the labeled sample yet.")
    if missed_sit_patterns:
        top = ', '.join(label for label, _ in missed_sit_patterns[:3])
        print(f"  Missed good/usable sits most often share: {top}.")
    else:
        print("  There are no missed good sits in the labeled sample yet.")
    if borderline_bust_rate > borderline_hit_rate:
        print("  Borderline calls currently look too aggressive.")
    elif borderline_hit_rate > borderline_bust_rate:
        print("  Borderline calls currently look conservative enough to find some usable starts.")
    else:
        print("  Borderline calls are evenly split between useful and bad outcomes so far.")
    print("  Treat these as diagnostic clues only; no recommendations are changed automatically.")
    return {'labeled_rows': len(work), 'groups': summaries}


def _decision_policy_risk_signals(row):
    """Pregame bust-risk signals used by decision-policy overlays."""
    signals = {}
    opp_rank = _safe_float(row.get('opp_rank'))
    park_factor = _safe_float(row.get('park_factor'))
    recent_era = _safe_float(row.get('recent_era'))
    proj_k9 = _safe_float(row.get('proj_k9') or row.get('k9'))
    workload = _safe_float(row.get('workload_risk_score'))
    pitch_matchup = _safe_float(row.get('pitch_matchup_score'))
    platoon = str(row.get('platoon') or '').lower()
    trend = str(row.get('trend') or '').lower()
    if trend == 'cold':
        signals['cold'] = True
    if recent_era is not None and recent_era >= 5.14:
        signals['recent_era>=5.14'] = True
    if opp_rank is not None and opp_rank <= 10:
        signals['top-10 offense'] = True
    if park_factor is not None and park_factor >= 1.05:
        signals['hitter park'] = True
    if platoon == 'risk':
        signals['platoon risk'] = True
    if proj_k9 is not None and proj_k9 < 7.5:
        signals['low K/9'] = True
    if workload is not None and workload >= 0.4:
        signals['workload risk'] = True
    if pitch_matchup is not None and pitch_matchup <= -0.05:
        signals['negative pitch matchup'] = True
    return signals


def _decision_policy_risk_score(row):
    """Legacy risk score used by the first visible risk guard."""
    signals = _decision_policy_risk_signals(row)
    score = 0
    reasons = []
    if signals.get('cold'):
        score += 2
        reasons.append('cold')
    for reason in (
        'recent_era>=5.14', 'top-10 offense', 'hitter park', 'platoon risk',
        'low K/9', 'workload risk', 'negative pitch matchup',
    ):
        if signals.get(reason):
            score += 1
            reasons.append(reason)
    return score, reasons


RISK_GUARD_WEIGHT_PRESETS = [
    {
        'key': 'risk_guard',
        'label': 'Current 2-flag risk guard',
        'description': 'Demote when legacy risk score reaches 2.',
        'threshold': 2.0,
        'weights': {
            'cold': 2.0,
            'recent_era>=5.14': 1.0,
            'top-10 offense': 1.0,
            'hitter park': 1.0,
            'platoon risk': 1.0,
            'low K/9': 1.0,
            'workload risk': 1.0,
            'negative pitch matchup': 1.0,
        },
    },
    {
        'key': 'weighted_risk_guard_v2',
        'label': 'Weighted risk guard v2',
        'description': 'Emphasize cold/recent ERA; demote at weighted score 3.',
        'threshold': 3.0,
        'weights': {
            'cold': 2.0,
            'recent_era>=5.14': 2.0,
            'top-10 offense': 1.0,
            'hitter park': 1.0,
            'platoon risk': 1.0,
            'low K/9': 1.0,
            'workload risk': 1.0,
            'negative pitch matchup': 1.0,
        },
    },
    {
        'key': 'weighted_risk_guard_v2_strict',
        'label': 'Weighted risk guard v2 strict',
        'description': 'Same weights as v2, but demote only at weighted score 4.',
        'threshold': 4.0,
        'weights': {
            'cold': 2.0,
            'recent_era>=5.14': 2.0,
            'top-10 offense': 1.0,
            'hitter park': 1.0,
            'platoon risk': 1.0,
            'low K/9': 1.0,
            'workload risk': 1.0,
            'negative pitch matchup': 1.0,
        },
    },
    {
        'key': 'form_first_risk_guard',
        'label': 'Form-first risk guard',
        'description': 'Make cold/recent ERA dominant; matchup-only stacks need more evidence.',
        'threshold': 3.0,
        'weights': {
            'cold': 2.5,
            'recent_era>=5.14': 2.0,
            'top-10 offense': 0.75,
            'hitter park': 0.75,
            'platoon risk': 0.75,
            'low K/9': 0.75,
            'workload risk': 1.0,
            'negative pitch matchup': 1.0,
        },
    },
]

RISK_GUARD_WEIGHT_PRESETS_BY_KEY = {
    preset['key']: preset for preset in RISK_GUARD_WEIGHT_PRESETS
}
VISIBLE_RISK_GUARD_POLICY_KEY = 'weighted_risk_guard_v2'


def _weighted_risk_guard_score(row, preset_or_key):
    preset = (
        RISK_GUARD_WEIGHT_PRESETS_BY_KEY.get(preset_or_key)
        if isinstance(preset_or_key, str) else preset_or_key
    )
    preset = preset or RISK_GUARD_WEIGHT_PRESETS_BY_KEY['risk_guard']
    signals = _decision_policy_risk_signals(row)
    score = 0.0
    reasons = []
    for reason, active in signals.items():
        if not active:
            continue
        weight = float(preset.get('weights', {}).get(reason, 0.0) or 0.0)
        if weight <= 0:
            continue
        score += weight
        reasons.append(reason)
    return round(score, 2), reasons


def _policy_from_points(row, start_threshold, borderline_threshold):
    pts = _safe_float(row.get('predicted_pts'))
    if pts is None:
        return row.get('predicted_advice') or 'UNKNOWN'
    if pts >= start_threshold:
        return 'START'
    if pts >= borderline_threshold:
        return 'BORDERLINE'
    return 'SIT'


def _demote_advice(advice):
    if advice == 'START':
        return 'BORDERLINE'
    if advice == 'BORDERLINE':
        return 'SIT'
    return advice


def _start_sit_policy_advice(row, policy_key):
    current = row.get('predicted_advice') or 'UNKNOWN'
    pts = _safe_float(row.get('predicted_pts'))
    risk_score, _reasons = _decision_policy_risk_score(row)
    trend = str(row.get('trend') or '').lower()
    recent_era = _safe_float(row.get('recent_era'))
    status_group = row.get('status_group') or _start_sit_status_group(row.get('status'))

    if policy_key == 'current':
        return current
    if policy_key == 'strict_start_11_9':
        return _policy_from_points(row, 11.0, 9.0)
    if policy_key == 'strict_start_12_9':
        return _policy_from_points(row, 12.0, 9.0)
    if policy_key == 'cold_overlay':
        if current in ('START', 'BORDERLINE') and (trend == 'cold' or (recent_era is not None and recent_era >= 5.14)):
            return _demote_advice(current)
        return current
    if policy_key == 'risk_guard':
        if current in ('START', 'BORDERLINE') and risk_score >= 2:
            return _demote_advice(current)
        return current
    if policy_key in RISK_GUARD_WEIGHT_PRESETS_BY_KEY:
        preset = RISK_GUARD_WEIGHT_PRESETS_BY_KEY[policy_key]
        weighted_score, _weighted_reasons = _weighted_risk_guard_score(row, preset)
        if current in ('START', 'BORDERLINE') and weighted_score >= preset['threshold']:
            return _demote_advice(current)
        return current
    if policy_key == 'streamer_conservative':
        advice = current
        if status_group == 'FA/WAIVER' and advice in ('START', 'BORDERLINE'):
            if risk_score >= 1 or (pts is not None and pts < 10.0):
                advice = _demote_advice(advice)
        return advice
    return current


def _shadow_risk_guard_decision(entry, features=None, policy_key=VISIBLE_RISK_GUARD_POLICY_KEY):
    """Analysis-only risk guard advice for logging/backtesting.

    This intentionally does not feed scoring, tiers, or report filtering.
    """
    features = features or {}
    row = dict(features)
    row.update({
        'predicted_pts': entry.get('pts'),
        'tier': entry.get('tier'),
        'status': entry.get('status'),
    })
    row['predicted_advice'] = _start_sit_predicted_advice(entry.get('tier'), entry.get('pts'))
    row['status_group'] = _start_sit_status_group(entry.get('status'))
    if policy_key in RISK_GUARD_WEIGHT_PRESETS_BY_KEY:
        risk_score, reasons = _weighted_risk_guard_score(row, policy_key)
    else:
        risk_score, reasons = _decision_policy_risk_score(row)
    shadow_advice = _start_sit_policy_advice(row, policy_key)
    return {
        'shadow_risk_guard_advice': shadow_advice,
        'shadow_risk_guard_changed': shadow_advice != row['predicted_advice'],
        'shadow_risk_guard_score': risk_score,
        'shadow_risk_guard_reasons': reasons,
        'shadow_risk_guard_policy': policy_key,
    }


def _decision_policy_metrics(df, advice_col):
    total = len(df)
    start = df[df[advice_col] == 'START']
    borderline = df[df[advice_col] == 'BORDERLINE']
    sit = df[df[advice_col] == 'SIT']
    start_bust = int((start['actual_pts'] < 5).sum())
    start_hit = int((start['actual_pts'] >= 8).sum())
    start_good = int((start['actual_pts'] >= 12).sum())
    sit_correct = int((sit['actual_pts'] < 8).sum())
    sit_missed = int((sit['actual_pts'] >= 12).sum())
    borderline_usable = int((borderline['actual_pts'] >= 8).sum())
    borderline_bust = int((borderline['actual_pts'] < 5).sum())
    playable = df[df[advice_col].isin(['START', 'BORDERLINE'])]
    negative_recommended = int((playable['actual_pts'] <= 0).sum())
    good_missed = sit_missed
    start_hit_rate = _start_sit_rate(start_hit, len(start))
    start_bust_rate = _start_sit_rate(start_bust, len(start))
    sit_missed_rate = _start_sit_rate(sit_missed, len(sit))
    borderline_bust_rate = _start_sit_rate(borderline_bust, len(borderline))
    # Conservative fantasy utility score: punish bad recommended starts more
    # than missed upside, because negative SP days can swing a matchup.
    utility = (
        start_hit
        + 0.5 * borderline_usable
        + 0.5 * sit_correct
        - 2.0 * start_bust
        - 1.5 * borderline_bust
        - 2.5 * negative_recommended
        - 1.0 * good_missed
    )
    return {
        'total': total,
        'start_count': len(start),
        'borderline_count': len(borderline),
        'sit_count': len(sit),
        'start_hit_rate': start_hit_rate,
        'start_good_rate': _start_sit_rate(start_good, len(start)),
        'start_bust_rate': start_bust_rate,
        'sit_correct_avoid_rate': _start_sit_rate(sit_correct, len(sit)),
        'sit_missed_opportunity_rate': sit_missed_rate,
        'borderline_usable_rate': _start_sit_rate(borderline_usable, len(borderline)),
        'borderline_bust_rate': borderline_bust_rate,
        'negative_recommended': negative_recommended,
        'good_starts_missed': good_missed,
        'utility_score': utility,
    }


def _policy_diff_outcome(row, from_advice, to_advice):
    actual = _safe_float(row.get('actual_pts'))
    if actual is None:
        return 'unknown'
    if from_advice == 'START' and to_advice == 'BORDERLINE':
        if actual < 5:
            return 'helped'
        if actual >= 12:
            return 'hurt'
        return 'neutral'
    if from_advice in ('START', 'BORDERLINE') and to_advice == 'SIT':
        if actual < 8:
            return 'helped'
        if actual >= 12:
            return 'hurt'
        return 'neutral'
    if from_advice == 'SIT' and to_advice in ('BORDERLINE', 'START'):
        if actual >= 12:
            return 'helped'
        if actual < 5:
            return 'hurt'
        return 'neutral'
    return 'neutral'


def _policy_diff_rows(work, policy_key):
    current_col = '_policy_current'
    policy_col = f'_policy_{policy_key}'
    if current_col not in work.columns:
        work[current_col] = [_start_sit_policy_advice(row, 'current') for _, row in work.iterrows()]
    if policy_col not in work.columns:
        work[policy_col] = [_start_sit_policy_advice(row, policy_key) for _, row in work.iterrows()]
    diffs = work[work[current_col] != work[policy_col]].copy()
    if diffs.empty:
        return diffs
    outcomes = []
    reason_texts = []
    risk_scores = []
    for _, row in diffs.iterrows():
        current = row[current_col]
        policy = row[policy_col]
        outcome = _policy_diff_outcome(row, current, policy)
        risk_score, reasons = _decision_policy_risk_score(row)
        outcomes.append(outcome)
        reason_texts.append('; '.join(reasons) if reasons else 'no logged risk reason')
        risk_scores.append(risk_score)
    diffs['_policy_outcome'] = outcomes
    diffs['_policy_reasons'] = reason_texts
    diffs['_policy_risk_score'] = risk_scores
    return diffs


def _print_policy_diff_examples(title, rows, policy_key, limit=6):
    print(f"\n{title}")
    if rows.empty:
        print("  None")
        return
    for _, row in rows.head(limit).iterrows():
        current = row.get('_policy_current')
        new_advice = row.get(f'_policy_{policy_key}') or '?'
        pred = _safe_float(row.get('predicted_pts'))
        pred_text = f"{pred:.1f}" if pred is not None else "--"
        actual = _safe_float(row.get('actual_pts'))
        actual_text = f"{actual:.1f}" if actual is not None else "--"
        print(
            f"  - {row.get('game_date') or '?'} | {row.get('pitcher_name') or '?'} "
            f"({row.get('team') or '?'} vs {row.get('opponent') or '?'}) "
            f"{current}->{new_advice} | pred {pred_text}, actual {actual_text} "
            f"| {row.get('_policy_reasons')}"
        )


def _print_policy_diff_analysis(work, policy_key, policy_label):
    diffs = _policy_diff_rows(work, policy_key)
    print(f"\nPolicy diff: {policy_label}")
    if diffs.empty:
        print("  No starts would change under this policy.")
        return {
            'changed': 0,
            'helped': 0,
            'hurt': 0,
            'neutral': 0,
            'reason_summary': [],
        }
    helped = diffs[diffs['_policy_outcome'] == 'helped']
    hurt = diffs[diffs['_policy_outcome'] == 'hurt']
    neutral = diffs[diffs['_policy_outcome'] == 'neutral']
    print(f"  starts changed: {len(diffs)}")
    print(f"  helped / hurt / neutral: {len(helped)} / {len(hurt)} / {len(neutral)}")
    transitions = diffs.groupby(['_policy_current', f'_policy_{policy_key}']).size().sort_values(ascending=False)
    print("  transitions:")
    for (from_advice, to_advice), count in transitions.items():
        print(f"    - {from_advice} -> {to_advice}: {int(count)}")

    from collections import Counter
    reason_counter = Counter()
    reason_help = Counter()
    reason_hurt = Counter()
    for _, row in diffs.iterrows():
        reasons = [r.strip() for r in str(row.get('_policy_reasons') or '').split(';') if r.strip()]
        for reason in reasons:
            reason_counter[reason] += 1
            if row.get('_policy_outcome') == 'helped':
                reason_help[reason] += 1
            elif row.get('_policy_outcome') == 'hurt':
                reason_hurt[reason] += 1
    print("  risk reason effectiveness:")
    reason_summary = []
    for reason, count in reason_counter.most_common(8):
        helped_n = reason_help[reason]
        hurt_n = reason_hurt[reason]
        reason_summary.append((reason, count, helped_n, hurt_n))
        print(f"    - {reason}: {count} demotions, helped {helped_n}, hurt {hurt_n}")

    _print_policy_diff_examples(
        "  Demotions that would have helped",
        helped.sort_values('actual_pts', ascending=True),
        policy_key,
    )
    _print_policy_diff_examples(
        "  Demotions that would have hurt",
        hurt.sort_values('actual_pts', ascending=False),
        policy_key,
    )
    return {
        'changed': int(len(diffs)),
        'helped': int(len(helped)),
        'hurt': int(len(hurt)),
        'neutral': int(len(neutral)),
        'reason_summary': reason_summary,
    }


def build_start_sit_policy_backtest_summary():
    """Build a compact, read-only decision-policy backtest summary."""
    work, source, skipped_source = _load_start_sit_analysis_rows()
    if work.empty:
        return {
            'available': False,
            'source': source,
            'skipped_source': skipped_source,
            'labeled_rows': 0,
            'note': 'No labeled starts with actual fantasy points are available yet.',
        }

    policies = [
        ('current', 'Current logged tiers', 'Use the recommendation tier exactly as logged.'),
        ('strict_start_11_9', 'Stricter thresholds 11/9', 'START at 11+ pts, BORDERLINE at 9-10.9, SIT below 9.'),
        ('strict_start_12_9', 'Very strict START 12/9', 'START at 12+ pts, BORDERLINE at 9-11.9, SIT below 9.'),
        ('cold_overlay', 'Cold/recent ERA overlay', 'Demote START/BORDERLINE one step when COLD or recent ERA >= 5.14.'),
        ('risk_guard', 'Risk guard overlay', 'Demote one step when two or more logged risk flags are present.'),
        (
            'weighted_risk_guard_v2',
            'Weighted risk guard v2',
            'Demote when weighted risk score reaches 3, emphasizing cold/recent ERA.',
        ),
        ('streamer_conservative', 'FA/waiver conservative', 'Demote FA/WAIVER streams with any risk flag or projection below 10.'),
    ]

    rows = []
    for key, label, description in policies:
        col = f'_policy_{key}'
        work[col] = [ _start_sit_policy_advice(row, key) for _, row in work.iterrows() ]
        metrics = _decision_policy_metrics(work, col)
        rows.append({'key': key, 'label': label, 'description': description, **metrics})

    rows_sorted = sorted(rows, key=lambda r: (-r['utility_score'], r['start_bust_rate'], r['good_starts_missed']))
    current = next((r for r in rows if r['key'] == 'current'), None)
    best = rows_sorted[0] if rows_sorted else None
    diff_summary = None
    if best and best['key'] != 'current':
        diffs = _policy_diff_rows(work, best['key'])
        if diffs.empty:
            diff_summary = {'changed': 0, 'helped': 0, 'hurt': 0, 'neutral': 0, 'reason_summary': []}
        else:
            helped = diffs[diffs['_policy_outcome'] == 'helped']
            hurt = diffs[diffs['_policy_outcome'] == 'hurt']
            neutral = diffs[diffs['_policy_outcome'] == 'neutral']
            from collections import Counter
            reason_counter = Counter()
            reason_help = Counter()
            reason_hurt = Counter()
            for _, row in diffs.iterrows():
                reasons = [r.strip() for r in str(row.get('_policy_reasons') or '').split(';') if r.strip()]
                for reason in reasons:
                    reason_counter[reason] += 1
                    if row.get('_policy_outcome') == 'helped':
                        reason_help[reason] += 1
                    elif row.get('_policy_outcome') == 'hurt':
                        reason_hurt[reason] += 1
            watched_reasons = {'recent_era>=5.14', 'cold', 'top-10 offense', 'platoon risk'}
            reason_summary = []
            seen_reasons = set()
            for reason in ('recent_era>=5.14', 'cold', 'top-10 offense', 'platoon risk'):
                if reason_counter.get(reason):
                    seen_reasons.add(reason)
                    reason_summary.append({
                        'reason': reason,
                        'demotions': int(reason_counter[reason]),
                        'helped': int(reason_help[reason]),
                        'hurt': int(reason_hurt[reason]),
                    })
            for reason, count in reason_counter.most_common(8):
                if reason in seen_reasons or reason in watched_reasons:
                    continue
                reason_summary.append({
                    'reason': reason,
                    'demotions': int(count),
                    'helped': int(reason_help[reason]),
                    'hurt': int(reason_hurt[reason]),
                })
                if len(reason_summary) >= 6:
                    break
            diff_summary = {
                'changed': int(len(diffs)),
                'helped': int(len(helped)),
                'hurt': int(len(hurt)),
                'neutral': int(len(neutral)),
                'reason_summary': reason_summary,
            }
    deltas = {}
    if current and best:
        deltas = {
            'start_bust_rate': round(best['start_bust_rate'] - current['start_bust_rate'], 1),
            'negative_recommended': int(best['negative_recommended'] - current['negative_recommended']),
            'good_starts_missed': int(best['good_starts_missed'] - current['good_starts_missed']),
        }
    return {
        'available': True,
        'source': source,
        'skipped_source': skipped_source,
        'labeled_rows': int(len(work)),
        'current': current,
        'best': best,
        'active_policy_key': VISIBLE_RISK_GUARD_POLICY_KEY,
        'active_policy_label': RISK_GUARD_WEIGHT_PRESETS_BY_KEY.get(
            VISIBLE_RISK_GUARD_POLICY_KEY, {}
        ).get('label', VISIBLE_RISK_GUARD_POLICY_KEY),
        'deltas': deltas,
        'diff_summary': diff_summary,
        'policies': rows_sorted,
        'note': 'Analysis only. Projected points and scoring are unchanged; visible recommendations may use the active risk guard overlay.',
    }


def _print_policy_comparison_table(rows_sorted):
    print("\nPolicy comparison")
    print(
        f"{'Policy':<26s} {'START/BORD/SIT':>16s} {'Start hit':>9s} "
        f"{'Start bust':>10s} {'Sit miss':>9s} {'Bord bust':>10s} "
        f"{'Neg rec':>7s} {'Good missed':>11s} {'Score':>8s}"
    )
    for r in rows_sorted:
        counts = f"{r['start_count']}/{r['borderline_count']}/{r['sit_count']}"
        print(
            f"{r['label']:<26s} {counts:>16s} "
            f"{r['start_hit_rate']:>8.1f}% {r['start_bust_rate']:>9.1f}% "
            f"{r['sit_missed_opportunity_rate']:>8.1f}% {r['borderline_bust_rate']:>9.1f}% "
            f"{r['negative_recommended']:>7d} {r['good_starts_missed']:>11d} "
            f"{r['utility_score']:>8.1f}"
        )


def analyze_start_sit_policy_backtest():
    """Read-only comparison of alternate start/sit decision policies."""
    print("START/SIT DECISION-RULE BACKTEST")
    print("=" * 60)
    print("Analysis only: this does not change scoring, predictions, tiers, recommendations, or learned corrections.")

    summary = build_start_sit_policy_backtest_summary()
    if summary.get('skipped_source'):
        print(f"Warehouse source skipped: {summary['skipped_source']}")
    print(f"Source: {summary.get('source')}")
    if not summary.get('available'):
        print(summary.get('note') or "No labeled starts with actual fantasy points are available yet.")
        return {'labeled_rows': 0, 'policies': []}

    work, _source, _skipped_source = _load_start_sit_analysis_rows()
    rows_sorted = summary.get('policies') or []
    current = summary.get('current')
    best = summary.get('best')

    print(f"\nLabeled starts analyzed: {summary['labeled_rows']}")
    if summary['labeled_rows'] < 100:
        print("Small-sample warning: fewer than 100 labeled decisions are available.")
    print("Fantasy utility score is directional only: it punishes recommended busts and negative starts more heavily than missed upside.")

    _print_policy_comparison_table(rows_sorted)

    print("\nPolicy notes")
    for r in rows_sorted:
        print(f"  - {r['label']}: {r['description']}")

    diff_summary = None
    if best and best['key'] != 'current':
        diff_summary = _print_policy_diff_analysis(work, best['key'], best['label'])

    print("\nInterpretation")
    if best:
        print(f"  Best backtested policy by conservative utility score: {best['label']}.")
    if current and best and best['key'] != 'current':
        print(
            "  Compared with current tiers, the best policy changed "
            f"START bust rate by {best['start_bust_rate'] - current['start_bust_rate']:+.1f} pts, "
            f"negative recommended starts by {best['negative_recommended'] - current['negative_recommended']:+d}, "
            f"and good starts missed by {best['good_starts_missed'] - current['good_starts_missed']:+d}."
        )
    elif best:
        print("  Current logged tiers are strongest among these simple policy tests by this conservative score.")

    if current:
        if current['start_bust_rate'] >= 30:
            print("  Current START recommendations have a high bust rate; future changes should protect against confident bad starts.")
        if current['borderline_bust_rate'] >= current['borderline_usable_rate']:
            print("  Borderline remains risky; avoid presenting it as a safe start.")
        if current['sit_missed_opportunity_rate'] >= 20:
            print("  There are meaningful missed SIT opportunities, so an overly strict policy may leave points on the bench.")
    if diff_summary:
        if diff_summary['hurt'] > diff_summary['helped']:
            print("  The best policy still has more costly demotions than saves by simple count; inspect the risk reasons before applying it.")
        elif diff_summary['helped']:
            print("  The best policy saved more bad decisions than it cost by simple count, but the missed upside still matters.")
    print("  Recommendation: use this to choose a policy later; nothing is automatically applied here.")
    return {'labeled_rows': len(work), 'policies': rows_sorted}


def _weighted_candidate_advice(row, weights, threshold):
    current = row.get('predicted_advice') or 'UNKNOWN'
    if current not in ('START', 'BORDERLINE'):
        return current
    signals = _decision_policy_risk_signals(row)
    score = sum(float(weights.get(reason, 0.0) or 0.0) for reason, active in signals.items() if active)
    return _demote_advice(current) if score >= threshold else current


def _weighted_candidate_diff(work, advice_col, weights):
    current_col = '_policy_current'
    if current_col not in work.columns:
        work[current_col] = [_start_sit_policy_advice(row, 'current') for _, row in work.iterrows()]
    diffs = work[work[current_col] != work[advice_col]].copy()
    if diffs.empty:
        return {'changed': 0, 'helped': 0, 'hurt': 0, 'neutral': 0, 'reason_summary': []}
    outcomes = []
    reason_summary = []
    from collections import Counter
    reason_counter = Counter()
    reason_help = Counter()
    reason_hurt = Counter()
    for _, row in diffs.iterrows():
        current = row[current_col]
        new_advice = row[advice_col]
        outcome = _policy_diff_outcome(row, current, new_advice)
        outcomes.append(outcome)
        signals = _decision_policy_risk_signals(row)
        reasons = [
            reason for reason, active in signals.items()
            if active and float(weights.get(reason, 0.0) or 0.0) > 0
        ] or ['no logged risk reason']
        for reason in reasons:
            reason_counter[reason] += 1
            if outcome == 'helped':
                reason_help[reason] += 1
            elif outcome == 'hurt':
                reason_hurt[reason] += 1
    for reason, count in reason_counter.most_common(8):
        reason_summary.append({
            'reason': reason,
            'demotions': int(count),
            'helped': int(reason_help[reason]),
            'hurt': int(reason_hurt[reason]),
        })
    return {
        'changed': int(len(diffs)),
        'helped': int(sum(1 for outcome in outcomes if outcome == 'helped')),
        'hurt': int(sum(1 for outcome in outcomes if outcome == 'hurt')),
        'neutral': int(sum(1 for outcome in outcomes if outcome == 'neutral')),
        'reason_summary': reason_summary,
    }


def analyze_risk_guard_weights():
    """Read-only comparison of weighted risk-guard recommendation overlays."""
    print("RISK GUARD WEIGHT ANALYSIS")
    print("=" * 60)
    print("Analysis only: this does not change scoring, projections, learned corrections, or roster moves.")

    work, source, skipped_source = _load_start_sit_analysis_rows()
    if skipped_source:
        print(f"Warehouse source skipped: {skipped_source}")
    print(f"Source: {source}")
    if work.empty:
        print("No labeled starts with actual fantasy points are available yet.")
        return {'labeled_rows': 0, 'policies': []}

    candidates = [
        {
            'key': 'current',
            'label': 'Current visible tiers',
            'threshold': None,
            'weights': {},
            'description': 'No risk-guard overlay.',
        }
    ]
    candidates.extend(RISK_GUARD_WEIGHT_PRESETS)
    v2_weights = RISK_GUARD_WEIGHT_PRESETS_BY_KEY['weighted_risk_guard_v2']['weights']
    form_weights = RISK_GUARD_WEIGHT_PRESETS_BY_KEY['form_first_risk_guard']['weights']
    for threshold in (2.5, 3.5, 4.5):
        candidates.append({
            'key': f'weighted_risk_guard_v2_t{str(threshold).replace(".", "_")}',
            'label': f'Weighted v2 threshold {threshold:g}',
            'description': f'Weighted v2 with demotion threshold {threshold:g}.',
            'threshold': threshold,
            'weights': v2_weights,
        })
    for threshold in (3.5, 4.0):
        candidates.append({
            'key': f'form_first_risk_guard_t{str(threshold).replace(".", "_")}',
            'label': f'Form-first threshold {threshold:g}',
            'description': f'Form-first weights with demotion threshold {threshold:g}.',
            'threshold': threshold,
            'weights': form_weights,
        })

    rows = []
    for candidate in candidates:
        key = candidate['key']
        col = f'_risk_weight_{key}'
        if key == 'current':
            work[col] = [_start_sit_policy_advice(row, 'current') for _, row in work.iterrows()]
        elif key in ('risk_guard', 'weighted_risk_guard_v2', 'weighted_risk_guard_v2_strict', 'form_first_risk_guard'):
            work[col] = [_start_sit_policy_advice(row, key) for _, row in work.iterrows()]
        else:
            weights = candidate.get('weights') or {}
            threshold = float(candidate.get('threshold') or 0)
            work[col] = [_weighted_candidate_advice(row, weights, threshold) for _, row in work.iterrows()]
        metrics = _decision_policy_metrics(work, col)
        diff = _weighted_candidate_diff(work, col, candidate.get('weights') or {})
        rows.append({
            **candidate,
            **metrics,
            'diff': diff,
        })

    rows_sorted = sorted(rows, key=lambda r: (-r['utility_score'], r['start_bust_rate'], r['good_starts_missed']))
    current = next((row for row in rows if row['key'] == 'current'), None)
    active = next((row for row in rows if row['key'] == VISIBLE_RISK_GUARD_POLICY_KEY), None)
    best = rows_sorted[0] if rows_sorted else None

    print(f"\nLabeled starts analyzed: {len(work)}")
    if len(work) < 100:
        print("Small-sample warning: fewer than 100 labeled decisions are available.")
    print(f"Active visible overlay: {VISIBLE_RISK_GUARD_POLICY_KEY}")
    print("\nRisk guard comparison")
    print(
        f"{'Policy':<31s} {'Thr':>5s} {'Changed':>7s} {'H/H/N':>9s} "
        f"{'Start bust':>10s} {'Neg rec':>7s} {'Good miss':>9s} {'Score':>8s}"
    )
    for row in rows_sorted:
        threshold = row.get('threshold')
        threshold_text = '-' if threshold is None else f"{float(threshold):.1f}"
        diff = row.get('diff') or {}
        hhn = f"{diff.get('helped', 0)}/{diff.get('hurt', 0)}/{diff.get('neutral', 0)}"
        print(
            f"{row['label']:<31s} {threshold_text:>5s} {diff.get('changed', 0):>7d} "
            f"{hhn:>9s} {row['start_bust_rate']:>9.1f}% {row['negative_recommended']:>7d} "
            f"{row['good_starts_missed']:>9d} {row['utility_score']:>8.1f}"
        )

    if best:
        print("\nBest by conservative utility score")
        print(f"  {best['label']}")
        print(f"  {best.get('description')}")
        if current and best['key'] != 'current':
            print(
                "  Compared with current tiers: "
                f"START bust {best['start_bust_rate'] - current['start_bust_rate']:+.1f} pts, "
                f"negative recommended {best['negative_recommended'] - current['negative_recommended']:+d}, "
                f"good starts missed {best['good_starts_missed'] - current['good_starts_missed']:+d}."
            )
    if active:
        print("\nActive overlay tradeoff")
        print(
            f"  {active['label']}: changed {active['diff']['changed']} starts; "
            f"helped/hurt/neutral {active['diff']['helped']}/{active['diff']['hurt']}/{active['diff']['neutral']}."
        )
        if current:
            print(
                f"  vs current tiers: negative recommended {current['negative_recommended']} -> "
                f"{active['negative_recommended']}; good starts missed {current['good_starts_missed']} -> "
                f"{active['good_starts_missed']}."
            )

    print("\nTop risk reasons for active overlay")
    active_reasons = (active or {}).get('diff', {}).get('reason_summary') or []
    if not active_reasons:
        print("  None")
    for reason in active_reasons[:8]:
        print(
            f"  - {reason['reason']}: {reason['demotions']} demotions, "
            f"helped {reason['helped']}, hurt {reason['hurt']}"
        )
    print("\nRecommendation")
    if best and active and best['key'] == active['key']:
        print("  Active weighted overlay is best among tested variants by this conservative score.")
    elif best and active:
        print(f"  Best tested variant is {best['label']}; active overlay is {active['label']}.")
    print("  This command is diagnostic; only the existing visible overlay uses the active policy key.")
    return {'labeled_rows': len(work), 'policies': rows_sorted}


FEATURE_REGISTRY = {}
WEATHER_VENUE_FEATURES = [
    'game_datetime', 'venue_name', 'venue_lat', 'venue_lon',
    'roof_type', 'roof_status', 'is_indoor_or_dome',
    'weather_source', 'weather_snapshot_time', 'weather_temp_f',
    'weather_wind_speed_mph', 'weather_wind_direction',
    'wind_out_to_cf_score', 'wind_in_from_cf_score', 'wind_cross_score',
    'weather_precip_prob', 'weather_humidity', 'weather_pressure',
    'weather_run_boost', 'weather_hr_boost', 'weather_note',
]
WORKLOAD_FEATURES = [
    'days_rest', 'last_pitch_count', 'last_start_ip', 'last_start_pitch_count',
    'avg_ip_last_3_starts', 'avg_pitch_count_last_3_starts',
    'max_pitch_count_last_5_starts', 'season_avg_ip_per_start',
    'season_avg_pitches_per_start', 'short_rest_flag', 'extra_rest_flag',
    'workload_risk_score', 'workload_note',
]


def _register_features(names, category, used_by=None, leakage_status='pregame_safe', logged=True):
    """Register prediction-log feature metadata for audit coverage."""
    for name in names:
        FEATURE_REGISTRY[name] = {
            'category': category,
            'used_by': list(used_by or ['prediction_log', 'feature_audit']),
            'leakage_status': leakage_status,
            'logged': logged,
        }


_register_features([
    'proj_era', 'proj_whip', 'proj_k9',
    'proj_ip', 'proj_gs', 'proj_w', 'proj_l', 'proj_so',
    'proj_h', 'proj_er', 'proj_bb', 'proj_bb9',
], 'projection', ['base_projection', 'learned_bias_scan', 'prediction_log'])

_register_features([
    'opp_ops', 'opp_ops_raw', 'opp_rank', 'opp_k_pct',
    'park_factor', 'park', 'platoon', 'opp_hand',
    'pitcher_hand', 'vs_l_ops', 'vs_r_ops', 'vs_l_ops_num', 'vs_r_ops_num',
    'splits_window_years', 'splits_l_r_diff',
    'combined_factor', 'opp_factor', 'pitch_matchup_score',
], 'matchup', ['base_projection', 'learned_bias_scan', 'prediction_log'])

_register_features([
    'tag', 'trend', 'recent_era', 'recent_ip', 'recent_k9',
    'fb_velo', 'pitch_count', 'emerging',
], 'form_and_pitcher_context', ['base_projection', 'learned_bias_scan', 'prediction_log'])

_register_features([
    'opp_il_count', 'opp_il_returns_count',
    'opp_bullpen_era', 'opp_bullpen_whip',
], 'opponent_context', ['base_projection', 'learned_bias_scan', 'prediction_log'])

_register_features([
    'xera', 'xwoba', 'xba', 'xslg', 'barrel_pct', 'hard_hit_pct',
    'whiff_pct', 'k_pct_savant', 'bb_pct_savant', 'chase_pct',
    'gb_pct', 'fb_pct', 'ld_pct',
], 'statcast', ['learned_bias_scan', 'prediction_log'])

_register_features([
    'stuff_plus', 'location_plus', 'pitching_plus',
    'fip', 'xfip', 'siera',
], 'fangraphs_advanced', ['learned_bias_scan', 'prediction_log'])

_register_features(WORKLOAD_FEATURES, 'workload', ['learned_bias_scan', 'prediction_log', 'future_model'])

_register_features(WEATHER_VENUE_FEATURES, 'weather_roof_environment', ['prediction_log', 'feature_audit', 'future_model'])

_register_features([
    'shadow_risk_guard_advice',
    'shadow_risk_guard_changed',
    'shadow_risk_guard_score',
    'shadow_risk_guard_reasons',
    'shadow_risk_guard_policy',
], 'decision_shadow_policy', ['prediction_log', 'feature_audit', 'future_policy_audit'])


def _recent_prediction_files(limit=5):
    if not os.path.isdir(PREDICTIONS_DIR):
        return []
    files = [
        os.path.join(PREDICTIONS_DIR, fn)
        for fn in os.listdir(PREDICTIONS_DIR)
        if fn.endswith('.jsonl')
    ]
    return sorted(files, reverse=True)[:limit]


def _modified_generated_files():
    patterns = [
        'engine/espn_players.json',
        'engine/learned_biases.json',
        'engine/predictions/*.jsonl',
        'engine/tracker_snapshots/*.json',
        'engine/streaming_cache/*.json',
        'engine/streaming_cache/**/*.json',
        'index.html',
        'tracker_report.html',
    ]
    try:
        res = subprocess.run(
            ['git', 'status', '--porcelain'],
            cwd=os.path.dirname(SCRIPT_DIR),
            check=False,
            capture_output=True,
            text=True,
        )
    except Exception:
        return []
    out = []
    for line in res.stdout.splitlines():
        if not line:
            continue
        path = line[3:].strip()
        if ' -> ' in path:
            path = path.split(' -> ', 1)[1].strip()
        if any(fnmatch.fnmatch(path, pat) for pat in patterns):
            out.append(line)
    return out


def audit_features():
    """Read recent prediction logs and report registry/logging consistency."""
    prediction_files = _recent_prediction_files(limit=5)
    observed = set()
    null_counts = {}
    total_records = 0

    for path in prediction_files:
        try:
            with open(path) as f:
                for line in f:
                    if not line.strip():
                        continue
                    try:
                        rec = json.loads(line)
                    except Exception:
                        continue
                    features = rec.get('features') or {}
                    total_records += 1
                    observed.update(features.keys())
                    for field in FEATURE_REGISTRY:
                        val = features.get(field)
                        if val is None or val == '':
                            null_counts[field] = null_counts.get(field, 0) + 1
        except Exception:
            continue

    registered = set(FEATURE_REGISTRY)
    used = {k for k, v in FEATURE_REGISTRY.items() if v.get('used_by')}
    logged = {k for k, v in FEATURE_REGISTRY.items() if v.get('logged')}
    known_leakage = {'pregame_safe', 'context', 'identifier', 'derived_pregame'}

    used_not_logged = sorted(used - logged)
    logged_not_used = sorted(logged - used)
    unknown_leakage = sorted(
        k for k, v in FEATURE_REGISTRY.items()
        if v.get('leakage_status') not in known_leakage
    )
    fields_missing_registry = sorted(observed - registered)
    registry_missing_recent = sorted(registered - observed)
    null_heavy = []
    if total_records:
        for field in sorted(registered & observed):
            n_null = null_counts.get(field, 0)
            if n_null / total_records >= 0.70:
                null_heavy.append((field, n_null, total_records, round(100 * n_null / total_records)))
    weather_coverage = []
    if total_records:
        for field in WEATHER_VENUE_FEATURES:
            present = total_records - null_counts.get(field, 0)
            weather_coverage.append((field, present, total_records, round(100 * present / total_records)))
    workload_coverage = []
    if total_records:
        for field in WORKLOAD_FEATURES:
            present = total_records - null_counts.get(field, 0)
            workload_coverage.append((field, present, total_records, round(100 * present / total_records)))

    def print_list(title, items, formatter=None):
        print(f"\n{title}")
        if not items:
            print("  None")
            return
        for item in items:
            print(f"  - {formatter(item) if formatter else item}")

    print("FEATURE AUDIT")
    print("=" * 60)
    print(f"Registry entries: {len(FEATURE_REGISTRY)}")
    print(f"Prediction files scanned: {len(prediction_files)}")
    for path in prediction_files:
        print(f"  - {path}")
    print(f"Prediction records scanned: {total_records}")
    print(f"Observed feature fields: {len(observed)}")

    print_list("Features used but not logged", used_not_logged)
    print_list("Features logged but not used", logged_not_used)
    print_list("Features with unknown leakage status", unknown_leakage)
    print_list("Prediction log fields missing from registry", fields_missing_registry)
    print_list("Registry features missing from recent predictions", registry_missing_recent)
    print_list(
        "Null-heavy features (threshold >= 70%)",
        null_heavy,
        lambda x: f"{x[0]}: {x[3]}% null/missing ({x[1]}/{x[2]})",
    )
    print_list(
        "Weather/venue/roof coverage",
        weather_coverage,
        lambda x: f"{x[0]}: {x[3]}% populated ({x[1]}/{x[2]})",
    )
    print_list(
        "Workload/leash coverage",
        workload_coverage,
        lambda x: f"{x[0]}: {x[3]}% populated ({x[1]}/{x[2]})",
    )
    print_list(
        "Generated/cache files modified but probably should not be committed",
        _modified_generated_files(),
    )


def log_prediction(entry):
    """Buffer a game-level prediction in memory; write to disk via
    flush_predictions() at the end of the run. Latest run wins for the same
    (pitcher, game_date) — multiple intraday runs simply update the buffer."""
    try:
        if entry.get('tbd') or entry.get('name') == 'TBD':
            return
        game_date = entry.get('date')
        pitcher_norm = normalize_name(entry.get('name', ''))
        if not game_date or not pitcher_norm:
            return
        logged_features = {
            # Core projection
            'proj_era': entry.get('era'),
            'proj_whip': entry.get('whip'),
            'proj_k9': entry.get('k9'),
            # Matchup
            'opp_ops': entry.get('opp_ops'),
            'opp_ops_raw': entry.get('opp_ops_raw'),
            'opp_rank': entry.get('opp_rank'),
            'opp_k_pct': entry.get('opp_k_pct'),
            'park_factor': entry.get('park_factor'),
            'park': entry.get('park'),
            'platoon': entry.get('platoon'),
            'opp_hand': entry.get('opp_hand'),
            'pitcher_hand': entry.get('pitcher_hand'),
            'vs_l_ops': entry.get('vs_l_ops'),
            'vs_r_ops': entry.get('vs_r_ops'),
            # Numeric versions so the auto-bucketing engine can quartile
            # and test for residual signal on platoon splits
            'vs_l_ops_num': _safe_float(entry.get('vs_l_ops')),
            'vs_r_ops_num': _safe_float(entry.get('vs_r_ops')),
            'splits_window_years': entry.get('splits_window_years'),
            'splits_l_r_diff': (
                (_safe_float(entry.get('vs_l_ops')) or 0)
                - (_safe_float(entry.get('vs_r_ops')) or 0)
            ) if entry.get('vs_l_ops') and entry.get('vs_r_ops') else None,
            'tag': entry.get('tag'),
            'trend': entry.get('trend'),
            'recent_era': entry.get('recent_era'),
            'fb_velo': entry.get('fb_velo'),
            'pitch_count': entry.get('pitch_count'),
            'emerging': entry.get('emerging'),
            'opp_il_count': len(entry.get('opp_il', []) or []),
            'opp_il_returns_count': len(entry.get('opp_il_returns', []) or []),
            # Statcast advanced (Phase 2)
            'xera': entry.get('xera'),
            'xwoba': entry.get('xwoba'),
            'xba': entry.get('xba'),
            'xslg': entry.get('xslg'),
            'barrel_pct': entry.get('barrel_pct'),
            'hard_hit_pct': entry.get('hard_hit_pct'),
            'whiff_pct': entry.get('whiff_pct'),
            'k_pct_savant': entry.get('k_pct_savant'),
            'bb_pct_savant': entry.get('bb_pct_savant'),
            'chase_pct': entry.get('chase_pct'),
            'gb_pct': entry.get('gb_pct'),
            'fb_pct': entry.get('fb_pct'),
            'ld_pct': entry.get('ld_pct'),
            # FG advanced (Phase 2)
            'stuff_plus': entry.get('stuff_plus'),
            'location_plus': entry.get('location_plus'),
            'pitching_plus': entry.get('pitching_plus'),
            'fip': entry.get('fip'),
            'xfip': entry.get('xfip'),
            'siera': entry.get('siera'),
            # Bullpen + workload (Phase 2)
            'opp_bullpen_era': entry.get('opp_bullpen_era'),
            'opp_bullpen_whip': entry.get('opp_bullpen_whip'),
            'days_rest': entry.get('days_rest'),
            'last_pitch_count': entry.get('last_pitch_count'),
            'last_start_ip': entry.get('last_start_ip'),
            'last_start_pitch_count': entry.get('last_start_pitch_count'),
            'avg_ip_last_3_starts': entry.get('avg_ip_last_3_starts'),
            'avg_pitch_count_last_3_starts': entry.get('avg_pitch_count_last_3_starts'),
            'max_pitch_count_last_5_starts': entry.get('max_pitch_count_last_5_starts'),
            'season_avg_ip_per_start': entry.get('season_avg_ip_per_start'),
            'season_avg_pitches_per_start': entry.get('season_avg_pitches_per_start'),
            'short_rest_flag': entry.get('short_rest_flag'),
            'extra_rest_flag': entry.get('extra_rest_flag'),
            'workload_risk_score': entry.get('workload_risk_score'),
            'workload_note': entry.get('workload_note'),
            # Logged-only weather/venue context. These are for audit and
            # later analysis only; they do not alter projected points.
            'game_datetime': entry.get('game_datetime'),
            'venue_name': entry.get('venue_name'),
            'venue_lat': entry.get('venue_lat'),
            'venue_lon': entry.get('venue_lon'),
            'roof_type': entry.get('roof_type'),
            'roof_status': entry.get('roof_status'),
            'is_indoor_or_dome': entry.get('is_indoor_or_dome'),
            'weather_source': entry.get('weather_source'),
            'weather_snapshot_time': entry.get('weather_snapshot_time'),
            'weather_temp_f': entry.get('weather_temp_f'),
            'weather_wind_speed_mph': entry.get('weather_wind_speed_mph'),
            'weather_wind_direction': entry.get('weather_wind_direction'),
            'wind_out_to_cf_score': entry.get('wind_out_to_cf_score'),
            'wind_in_from_cf_score': entry.get('wind_in_from_cf_score'),
            'wind_cross_score': entry.get('wind_cross_score'),
            'weather_precip_prob': entry.get('weather_precip_prob'),
            'weather_humidity': entry.get('weather_humidity'),
            'weather_pressure': entry.get('weather_pressure'),
            'weather_run_boost': entry.get('weather_run_boost'),
            'weather_hr_boost': entry.get('weather_hr_boost'),
            'weather_note': entry.get('weather_note'),
        }
        logged_features.update(_shadow_risk_guard_decision(entry, logged_features))
        record = {
            'logged_at': datetime.now().isoformat(timespec='seconds'),
            'date': game_date,
            'name': entry.get('name'),
            'team': entry.get('team'),
            'opponent': entry.get('opponent'),
            'home_away': entry.get('home_away'),
            'game_pk': entry.get('game_pk'),
            'pitcher_id': entry.get('pitcher_id'),
            'pitcher_hand': entry.get('pitcher_hand'),
            # predicted_pts is the FINAL number we're committing to (post-learning)
            'predicted_pts': entry.get('pts'),
            # predicted_pts_raw is the rule-based prediction BEFORE learned
            # adjustments. Used for future bias detection so the learning
            # loop never feeds on its own outputs.
            'predicted_pts_raw': entry.get('pts_pre_adj', entry.get('pts')),
            'adj_total': entry.get('adj_total', 0.0),
            'adjustments': entry.get('adjustments', []),
            'base_pts': entry.get('base_pts'),
            'tier': entry.get('tier'),
            'status': entry.get('status'),
            'features': logged_features,
        }
        record['features'] = _features_with_venue_metadata(record.get('features'), record)
        _runtime_prediction_records.append(dict(record))
        # Buffer in memory; flush_predictions() writes one JSONL per date at
        # end of run. Avoids thousands of small files which slow git ops.
        _pending_predictions[(game_date, pitcher_norm)] = record
    except Exception as e:
        # Logging must never break the tracker run
        print(f"  [predict-log] {e}")


def flush_predictions():
    """Persist buffered predictions to disk. Writes one JSONL file per game
    date, merging with any existing entries (updating same-pitcher records
    with the freshest one)."""
    if not _pending_predictions:
        return
    if PREVIEW_LOCAL:
        print("  Local preview mode: skipping prediction log write")
        _pending_predictions.clear()
        return
    by_date = {}
    for (gd, pname), rec in _pending_predictions.items():
        by_date.setdefault(gd, {})[pname] = rec
    os.makedirs(PREDICTIONS_DIR, exist_ok=True)
    for gd, recs in by_date.items():
        path = os.path.join(PREDICTIONS_DIR, f'{gd}.jsonl')
        existing = {}
        # Pull in any legacy per-pitcher .json files for this date so we
        # consolidate into the JSONL and they don't get processed twice
        legacy_dir = os.path.join(PREDICTIONS_DIR, gd)
        if os.path.isdir(legacy_dir):
            for fn in os.listdir(legacy_dir):
                if not fn.endswith('.json'):
                    continue
                try:
                    with open(os.path.join(legacy_dir, fn)) as f:
                        r = json.load(f)
                    key = normalize_name(r.get('name', ''))
                    if key:
                        existing[key] = r
                except Exception:
                    continue
        if os.path.exists(path):
            try:
                with open(path) as f:
                    for line in f:
                        try:
                            r = json.loads(line)
                        except Exception:
                            continue
                        key = normalize_name(r.get('name', ''))
                        if key:
                            existing[key] = r
            except Exception:
                pass
        existing.update(recs)  # current run wins over both legacy and prior JSONL
        try:
            with open(path, 'w') as f:
                for rec in existing.values():
                    f.write(json.dumps(rec) + '\n')
            # Now safe to delete the legacy directory — its contents are
            # merged into the JSONL.
            if os.path.isdir(legacy_dir):
                import shutil
                shutil.rmtree(legacy_dir)
            try:
                parquet_path = wh_write_prediction_parquet(gd, list(existing.values()))
                print(f"  [warehouse] predictions mirrored: {parquet_path}")
                feature_path = wh_write_sp_start_features_parquet(gd, list(existing.values()))
                print(f"  [warehouse] SP start features mirrored: {feature_path}")
            except Exception as wh_err:
                print(f"  [warehouse] prediction mirror skipped for {gd}: {wh_err}")
        except Exception as e:
            print(f"  [flush-predictions] {gd}: {e}")
    _pending_predictions.clear()


def actual_pitcher_pts(line):
    """Compute fantasy points from a completed boxscore line using the user's
    league scoring (IP*3, K*1, W*5, H*-1, ER*-2, BB*-1, L*-5)."""
    ip = line.get('IP', 0) or 0
    h = line.get('H', 0) or 0
    er = line.get('ER', 0) or 0
    bb = line.get('BB', 0) or 0
    k = line.get('K', 0) or 0
    decision = line.get('decision', '')
    w = 1 if decision == 'W' else 0
    l = 1 if decision == 'L' else 0
    return ip * 3 + k * 1 + w * 5 + h * -1 + er * -2 + bb * -1 + l * -5


def process_pending_outcomes():
    """For every prediction directory whose game date is already in the past,
    fetch actual SP lines from MLB boxscores, join with each prediction,
    append a record to OUTCOMES_LOG, and DELETE the prediction file.
    The outcomes log is the single source of truth — no need to archive
    individual prediction files (which used to balloon git's index).
    Handles both new format (predictions/{date}.jsonl) and legacy format
    (predictions/{date}/{pitcher}.json directories).
    Returns the number of outcomes newly recorded."""
    if not os.path.isdir(PREDICTIONS_DIR):
        return 0
    import shutil
    today = date.today().isoformat()
    new_records = 0
    mirrored_dates = set()

    def _join_and_log(pred, outcome_dict):
        nonlocal new_records
        pname = normalize_name(pred.get('name', ''))
        outcome = outcome_dict.get(pname)
        if not outcome:
            joined = {**pred, 'actual_line': None, 'actual_pts': None,
                      'residual': None, 'no_start': True}
        else:
            actual = actual_pitcher_pts(outcome)
            pred_final = pred.get('predicted_pts') or 0
            pred_raw = pred.get('predicted_pts_raw', pred_final)
            joined = {
                **pred,
                'actual_line': outcome,
                'actual_pts': round(actual, 2),
                'residual_raw': round(actual - pred_raw, 2),
                'residual': round(actual - pred_final, 2),
                'no_start': False,
            }
        with open(OUTCOMES_LOG, 'a') as f:
            f.write(json.dumps(joined) + '\n')
        mirrored_dates.add(joined.get('date'))
        new_records += 1

    for entry in sorted(os.listdir(PREDICTIONS_DIR)):
        full_path = os.path.join(PREDICTIONS_DIR, entry)

        # Legacy: directory of per-pitcher JSON files
        if os.path.isdir(full_path):
            d = entry
            if d.startswith('.') or not re.match(r'^\d{4}-\d{2}-\d{2}$', d):
                # Scrub the old .processed/ tree if it exists
                if entry == '.processed':
                    try:
                        shutil.rmtree(full_path)
                    except Exception:
                        pass
                continue
            if d >= today:
                continue
            outcomes = fetch_completed_starts_for_date(d, verbose=False)
            if not outcomes:
                continue
            for fn in os.listdir(full_path):
                if not fn.endswith('.json'):
                    continue
                try:
                    with open(os.path.join(full_path, fn)) as f:
                        pred = json.load(f)
                except Exception:
                    continue
                _join_and_log(pred, outcomes)
            try:
                shutil.rmtree(full_path)
            except Exception:
                pass

        # New format: predictions/{date}.jsonl
        elif entry.endswith('.jsonl'):
            d = entry[:-len('.jsonl')]
            if not re.match(r'^\d{4}-\d{2}-\d{2}$', d):
                continue
            if d >= today:
                continue
            outcomes = fetch_completed_starts_for_date(d, verbose=False)
            if not outcomes:
                continue
            try:
                with open(full_path) as f:
                    for line in f:
                        try:
                            pred = json.loads(line)
                        except Exception:
                            continue
                        _join_and_log(pred, outcomes)
            except Exception:
                continue
            try:
                os.remove(full_path)
            except Exception:
                pass

    for d in sorted(x for x in mirrored_dates if x):
        try:
            parquet_path = wh_write_outcome_parquet(d)
            if parquet_path:
                print(f"  [warehouse] outcomes mirrored: {parquet_path}")
        except Exception as wh_err:
            print(f"  [warehouse] outcome mirror skipped for {d}: {wh_err}")

    return new_records


def calibration_stats(window_days=30):
    """Compute rolling accuracy over the last N days. Returns dict with MAE,
    RMSE, bias, per-tier means, and the most over/under-predicted starts."""
    if not os.path.exists(OUTCOMES_LOG):
        return None
    cutoff = (date.today() - timedelta(days=window_days)).isoformat()
    samples = []
    try:
        with open(OUTCOMES_LOG) as f:
            for line in f:
                try:
                    rec = json.loads(line)
                except Exception:
                    continue
                if rec.get('no_start') or rec.get('residual') is None:
                    continue
                if rec.get('date', '0') >= cutoff:
                    samples.append(rec)
    except Exception:
        return None
    if not samples:
        return None

    diffs = [s['residual'] for s in samples]
    abs_diffs = [abs(d) for d in diffs]
    n = len(samples)
    mae = sum(abs_diffs) / n
    rmse = (sum(d * d for d in diffs) / n) ** 0.5
    bias = sum(diffs) / n  # positive = we underpredict; negative = overpredict

    # Per-tier accuracy: was the recommendation borne out?
    by_tier = {}
    for s in samples:
        t = s.get('tier', 'unknown')
        by_tier.setdefault(t, []).append(s)
    tier_summary = {}
    for t, items in by_tier.items():
        n_t = len(items)
        tier_summary[t] = {
            'count': n_t,
            'mean_predicted': round(sum((it.get('predicted_pts') or 0) for it in items) / n_t, 2),
            'mean_actual': round(sum(it['actual_pts'] for it in items) / n_t, 2),
            'mean_residual': round(sum(it['residual'] for it in items) / n_t, 2),
        }

    sorted_by_residual = sorted(samples, key=lambda s: s['residual'])
    worst = sorted_by_residual[:5]   # we said go, they bombed
    best = sorted_by_residual[-5:]   # we underestimated

    def _slim(s):
        return {
            'date': s.get('date'),
            'name': s.get('name'),
            'opponent': s.get('opponent'),
            'tier': s.get('tier'),
            'predicted_pts': s.get('predicted_pts'),
            'actual_pts': s.get('actual_pts'),
            'residual': s.get('residual'),
        }

    return {
        'n': n,
        'window_days': window_days,
        'mae': round(mae, 2),
        'rmse': round(rmse, 2),
        'bias': round(bias, 2),
        'by_tier': tier_summary,
        'worst_overpredictions': [_slim(x) for x in worst],
        'best_underpredictions': [_slim(x) for x in reversed(best)],
    }


def _residual_stats(samples, residual_key='residual_raw'):
    """Compute n, mean residual, std, z-score for a list of joined records.
    Uses residual_raw by default (rule-based prediction vs actual) so the
    learning loop never feeds on its own learned-adjusted outputs."""
    rs = []
    for s in samples:
        r = s.get(residual_key)
        if r is None:
            r = s.get('residual')  # back-compat for older records
        if r is None:
            continue
        rs.append(r)
    n = len(rs)
    if n == 0:
        return None
    mean = sum(rs) / n
    if n < 2:
        return {'n': n, 'mean': round(mean, 2), 'std': 0.0, 'se': None, 'z': None}
    var = sum((r - mean) ** 2 for r in rs) / (n - 1)
    std = var ** 0.5
    se = std / (n ** 0.5) if std >= MIN_RESIDUAL_STD else None
    z = mean / se if se and se > 0 else None
    if z is not None and (not math.isfinite(z) or abs(z) > MAX_ABS_LEARNED_Z):
        z = None
    return {
        'n': n,
        'mean': round(mean, 2),
        'std': round(std, 2),
        'se': round(se, 4) if se is not None else None,
        'z': round(z, 2) if z is not None and math.isfinite(z) else None,
    }


def _is_missing_value(value):
    if value is None:
        return True
    try:
        return bool(pd.isna(value))
    except (TypeError, ValueError):
        return False


def _valid_learning_outcome(record):
    return not record.get('no_start') and (
        record.get('residual_raw') is not None or record.get('residual') is not None
    )


def _parse_learning_datetime(value):
    if not value:
        return None
    try:
        text = str(value).strip()
        if not text:
            return None
        if text.endswith('Z'):
            text = text[:-1] + '+00:00'
        dt = datetime.fromisoformat(text)
        return dt.replace(tzinfo=None)
    except Exception:
        return None


def _learning_logged_at(record):
    return _parse_learning_datetime(record.get('logged_at') or record.get('snapshot_time'))


def _learning_game_time(record):
    features = record.get('features') or {}
    return _parse_learning_datetime(
        record.get('game_datetime')
        or record.get('game_time')
        or features.get('game_datetime')
        or features.get('game_time')
    )


def _choose_learning_representative(items):
    """Pick latest pregame prediction snapshot from one actual-start group."""
    before_game = []
    with_logged_at = []
    for idx, rec in items:
        logged_at = _learning_logged_at(rec)
        game_time = _learning_game_time(rec)
        if logged_at is not None:
            with_logged_at.append((logged_at, idx, rec))
            if game_time is not None and logged_at <= game_time:
                before_game.append((logged_at, idx, rec))
    if before_game:
        return max(before_game, key=lambda item: (item[0], item[1]))[2]
    if with_logged_at:
        return max(with_logged_at, key=lambda item: (item[0], item[1]))[2]
    return max(items, key=lambda item: item[0])[1]


def select_learning_outcome_samples(records):
    """Collapse duplicate/snapshot outcome rows to one sample per actual start."""
    exact_seen = set()
    exact_unique = []
    for idx, rec in enumerate(records):
        key = _outcome_exact_duplicate_key(rec)
        if key in exact_seen:
            continue
        exact_seen.add(key)
        exact_unique.append((idx, rec))

    eligible = [(idx, rec) for idx, rec in exact_unique if _valid_learning_outcome(rec)]
    grouped = {}
    for idx, rec in eligible:
        grouped.setdefault(_outcome_stable_duplicate_key(rec), []).append((idx, rec))

    samples = []
    snapshot_groups_collapsed = 0
    snapshot_rows_removed = 0
    for items in grouped.values():
        if len(items) > 1:
            snapshot_groups_collapsed += 1
            snapshot_rows_removed += len(items) - 1
        samples.append(_choose_learning_representative(items))

    stats = {
        'raw_rows': len(records),
        'exact_duplicates_removed': len(records) - len(exact_unique),
        'exact_unique_rows': len(exact_unique),
        'rows_excluded_before_learning': len(exact_unique) - len(eligible),
        'eligible_rows_after_exact_dedupe': len(eligible),
        'unique_actual_starts': len(samples),
        'snapshot_groups_collapsed': snapshot_groups_collapsed,
        'snapshot_rows_removed': snapshot_rows_removed,
    }
    return samples, stats


def _load_outcomes_from_jsonl_for_learning(return_stats=False):
    """Load all joined outcome records from the JSONL source of truth."""
    if not os.path.exists(OUTCOMES_LOG):
        empty = {
            'raw_rows': 0,
            'exact_duplicates_removed': 0,
            'exact_unique_rows': 0,
            'rows_excluded_before_learning': 0,
            'eligible_rows_after_exact_dedupe': 0,
            'unique_actual_starts': 0,
            'snapshot_groups_collapsed': 0,
            'snapshot_rows_removed': 0,
        }
        return ([], empty) if return_stats else []
    out = []
    try:
        with open(OUTCOMES_LOG) as f:
            for line in f:
                try:
                    s = json.loads(line)
                except Exception:
                    continue
                out.append(s)
    except Exception:
        pass
    samples, stats = select_learning_outcome_samples(out)
    return (samples, stats) if return_stats else samples


def _warehouse_row_to_learning_outcome(row):
    """Restore flattened outcome Parquet rows to the JSONL-like learning shape."""
    rec = {}
    features = {}
    for key, value in row.items():
        if _is_missing_value(value):
            value = None
        if key in FEATURE_REGISTRY:
            if value is not None:
                features[key] = value
            continue
        if key.startswith('feature_'):
            feature_key = key[len('feature_'):]
            if value is not None:
                features[feature_key] = value
            continue
        rec[key] = value
    if isinstance(rec.get('actual_line'), str):
        try:
            rec['actual_line'] = json.loads(rec['actual_line'])
        except Exception:
            pass
    if not rec.get('date') and rec.get('game_date'):
        rec['date'] = rec.get('game_date')
    if not rec.get('name') and rec.get('pitcher_name'):
        rec['name'] = rec.get('pitcher_name')
    if features:
        rec['features'] = features
    return rec


def _load_outcomes_from_warehouse_for_learning(return_stats=False):
    """Read learned-bias inputs from outcome Parquet partitions when present."""
    empty = {
        'raw_rows': 0,
        'exact_duplicates_removed': 0,
        'exact_unique_rows': 0,
        'rows_excluded_before_learning': 0,
        'eligible_rows_after_exact_dedupe': 0,
        'unique_actual_starts': 0,
        'snapshot_groups_collapsed': 0,
        'snapshot_rows_removed': 0,
    }
    if not _warehouse_parquet_files('outcomes'):
        return ([], empty) if return_stats else []
    try:
        import duckdb
        conn = duckdb.connect(database=':memory:')
        outcome_glob = _sql_path(os.path.join(wh_path('outcomes'), '*.parquet'))
        df = conn.execute(
            f"SELECT * FROM read_parquet('{outcome_glob}', union_by_name=true)"
        ).fetchdf()
        conn.close()
    except Exception as e:
        print(f"Learning outcomes warehouse load failed; using JSONL fallback ({type(e).__name__}: {e})")
        return ([], empty) if return_stats else []

    out = []
    for row in df.to_dict('records'):
        rec = _warehouse_row_to_learning_outcome(row)
        out.append(rec)
    samples, stats = select_learning_outcome_samples(out)
    return (samples, stats) if return_stats else samples


def _learning_outcome_source_counts():
    _, jsonl_stats = _load_outcomes_from_jsonl_for_learning(return_stats=True)
    _, parquet_stats = _load_outcomes_from_warehouse_for_learning(return_stats=True)
    return jsonl_stats, parquet_stats


def _load_outcomes_for_learning(return_stats=False):
    """Load joined outcome records for learned-bias scanning."""
    warehouse_records, warehouse_stats = _load_outcomes_from_warehouse_for_learning(return_stats=True)
    if warehouse_records:
        if os.path.exists(OUTCOMES_LOG):
            _, jsonl_stats = _load_outcomes_from_jsonl_for_learning(return_stats=True)
            print(
                "Learning outcome count check: "
                f"jsonl={jsonl_stats['unique_actual_starts']} parquet={warehouse_stats['unique_actual_starts']}"
            )
        print(
            "Learning sample selection: "
            f"{warehouse_stats['raw_rows']} outcome rows -> {warehouse_stats['unique_actual_starts']} unique starts "
            f"({warehouse_stats['exact_duplicates_removed']} exact duplicate rows removed, "
            f"{warehouse_stats['snapshot_rows_removed']} snapshot rows collapsed)"
        )
        print("Learning outcomes loaded from warehouse Parquet")
        return (warehouse_records, warehouse_stats) if return_stats else warehouse_records

    jsonl_records, jsonl_stats = _load_outcomes_from_jsonl_for_learning(return_stats=True)
    print(
        "Learning sample selection: "
        f"{jsonl_stats['raw_rows']} outcome rows -> {jsonl_stats['unique_actual_starts']} unique starts "
        f"({jsonl_stats['exact_duplicates_removed']} exact duplicate rows removed, "
        f"{jsonl_stats['snapshot_rows_removed']} snapshot rows collapsed)"
    )
    print("Learning outcomes loaded from JSONL fallback")
    if _warehouse_parquet_files('outcomes'):
        print(f"Learning outcome count check: jsonl={jsonl_stats['unique_actual_starts']} parquet=0")
    return (jsonl_records, jsonl_stats) if return_stats else jsonl_records


GENERAL_BUCKET_MIN_SAMPLES = 20
TREND_BUCKET_MIN_SAMPLES = 20
PITCHER_BUCKET_MIN_SAMPLES = 12
MIN_RESIDUAL_STD = 1.0
MAX_ABS_LEARNED_Z = 8.0
MAX_LEARNED_ADJ = 5.0
GENERAL_SHRINK_N = 60
PITCHER_SHRINK_N = 48
NUMERIC_AUTO_BUCKET_FEATURES = [
    # Core projection features
    'proj_era', 'proj_whip', 'proj_k9',
    # Recent form
    'recent_era',
    # Matchup
    'opp_rank', 'park_factor',
    # Arsenal
    'fb_velo', 'pitch_count',
    # IL
    'opp_il_count', 'opp_il_returns_count',
    # Statcast advanced (populated as new data flows in)
    'xera', 'xwoba', 'xba', 'xslg', 'barrel_pct', 'hard_hit_pct',
    'whiff_pct', 'k_pct_savant', 'bb_pct_savant', 'chase_pct',
    'gb_pct', 'fb_pct', 'ld_pct',
    # FG advanced
    'stuff_plus', 'location_plus', 'pitching_plus', 'fip', 'xfip', 'siera',
    # Workload
    'days_rest', 'last_pitch_count',
    # Bullpen
    'opp_bullpen_era', 'opp_bullpen_whip',
    # Platoon splits (numeric so auto-bucketing can find aging-vet patterns)
    'vs_l_ops_num', 'vs_r_ops_num', 'splits_l_r_diff', 'splits_window_years',
]


def _auto_bucket_continuous(samples, fname, n_buckets=4):
    """Auto-quartile any numeric feature, return list of (bucket_samples, label, lo, hi).
    Skips features with fewer than n_buckets * 5 samples (need enough to bucket)."""
    vals = []
    for s in samples:
        v = (s.get('features') or {}).get(fname)
        if v is None or not isinstance(v, (int, float)):
            continue
        vals.append(v)
    if len(vals) < n_buckets * 5:
        return []
    sorted_vals = sorted(vals)
    boundaries = [sorted_vals[int(i * len(sorted_vals) / n_buckets)] for i in range(1, n_buckets)]
    boundaries = [-float('inf')] + boundaries + [float('inf')]
    out = []
    for i in range(len(boundaries) - 1):
        lo, hi = boundaries[i], boundaries[i + 1]
        bucket = [s for s in samples
                  if (s.get('features') or {}).get(fname) is not None
                  and lo <= s['features'][fname] < hi]
        # Pretty range label
        if lo == -float('inf'):
            lbl = f"{fname} ≤ {hi:.2f}"
        elif hi == float('inf'):
            lbl = f"{fname} ≥ {lo:.2f}"
        else:
            lbl = f"{fname} in [{lo:.2f}, {hi:.2f})"
        out.append((bucket, lbl, lo, hi))
    return out


def compute_learned_biases(min_samples=GENERAL_BUCKET_MIN_SAMPLES, min_abs_delta=0.5, base_alpha=0.01):
    """Scan accumulated outcomes for systematic biases in feature buckets.

    Statistical rigor (so we don't fire on noise):
      - Multiple-comparisons correction: z threshold scales with #buckets tested
        via approximate Bonferroni. With 50 tests at α=0.01, effective z ≈ 4.1.
        With more features, the bar gets stricter — protects against the
        "data dredging" failure mode.
      - Each bucket's adjustment is shrunk toward zero, then clamped to
        ±MAX_LEARNED_ADJ, so no single correlation can dominate.
      - Per-pitcher buckets require a larger sample than before and get
        stronger shrinkage because individual starts are noisy.
    """
    samples, learning_stats = _load_outcomes_for_learning(return_stats=True)
    if not samples:
        return {}

    biases = {}
    candidates = []  # close to threshold, too-small, or otherwise ineligible
    test_count = 0

    def passes_threshold(z, n_tests):
        if z is None or not isinstance(z, (int, float)) or not math.isfinite(z):
            return False
        if abs(z) > MAX_ABS_LEARNED_Z:
            return False
        # Bonferroni-style: more tests → higher bar. Floor at 2.5 for sanity.
        if n_tests <= 1:
            return abs(z) >= 2.5
        # Approx z for Bonferroni-corrected α/n_tests, two-tailed.
        # For α=0.01 and ~50 tests: z ≈ 4.1. For ~100 tests: z ≈ 4.3.
        # Use simple formula z = sqrt(2 * ln(n_tests / α))
        try:
            corrected_z = math.sqrt(2 * math.log(n_tests / base_alpha))
        except (ValueError, ZeroDivisionError):
            corrected_z = 3.0
        return abs(z) >= max(2.5, corrected_z)

    def min_n_for_basis(basis):
        if basis == 'pitcher':
            return max(PITCHER_BUCKET_MIN_SAMPLES, 12)
        if basis == 'trend':
            return max(TREND_BUCKET_MIN_SAMPLES, 20)
        return max(min_samples, GENERAL_BUCKET_MIN_SAMPLES, 20)

    def shrink_delta(mean, n, basis):
        shrink_n = PITCHER_SHRINK_N if basis == 'pitcher' else GENERAL_SHRINK_N
        shrunk = mean * (n / (n + shrink_n)) if n > 0 else 0.0
        return round(max(-MAX_LEARNED_ADJ, min(MAX_LEARNED_ADJ, shrunk)), 2)

    def ineligible_reasons(st, basis, n_tests, min_abs):
        reasons = []
        min_n = min_n_for_basis(basis)
        if st['n'] < min_n:
            reasons.append(f'n<{min_n}')
        if abs(st['mean']) < min_abs:
            reasons.append(f'|mean|<{min_abs}')
        if st.get('std') is None or st.get('std') < MIN_RESIDUAL_STD:
            reasons.append(f'std<{MIN_RESIDUAL_STD:g}')
        se = st.get('se')
        if se is None or not isinstance(se, (int, float)) or not math.isfinite(se) or se <= 0:
            reasons.append('invalid standard error')
        z = st.get('z')
        if z is None or not isinstance(z, (int, float)) or not math.isfinite(z):
            reasons.append('invalid z-score')
        elif abs(z) > MAX_ABS_LEARNED_Z:
            reasons.append(f'abs(z)>{MAX_ABS_LEARNED_Z:g}')
        elif not passes_threshold(z, n_tests):
            reasons.append('z below activation threshold')
        return reasons

    def maybe_add(key, bucket, basis, label_tmpl, min_abs=None):
        nonlocal test_count
        test_count += 1
        min_abs = min_abs_delta if min_abs is None else min_abs
        st = _residual_stats(bucket)
        if not st:
            return
        label = label_tmpl.format(delta=st['mean'], n=st['n'])
        rec = {**st, 'basis': basis, 'key': key, 'label': label}
        reasons = ineligible_reasons(st, basis, 50, min_abs)
        if reasons:
            rec['eligible'] = False
            rec['ineligible_reason'] = ', '.join(reasons)
            # Keep interesting-but-unsafe buckets visible without activating
            # them, including small-n or low-variance pitcher buckets.
            if abs(st['mean']) >= min_abs and st['n'] >= max(3, min_n_for_basis(basis) // 2):
                rec['applied_delta'] = 0.0
                candidates.append(rec)
            elif st.get('z') is not None and abs(st['z']) >= 1.5:
                rec['applied_delta'] = 0.0
                candidates.append(rec)
            return

        rec['eligible'] = True
        rec['applied_delta'] = shrink_delta(st['mean'], st['n'], basis)
        # Keep mean as the raw residual mean; applied_delta is the actual
        # shrunk/capped learned adjustment.
        biases[key] = rec

    # 1. Per-tier bias
    for tier in ('must_start', 'start', 'borderline', 'avoid'):
        bucket = [s for s in samples if s.get('tier') == tier]
        maybe_add(f'tier_{tier}', bucket, 'tier',
                   f'{tier.replace("_"," ").title()} tier averaging {{delta:+.1f}} pts vs prediction (n={{n}})')

    # 2. Per opp_rank bracket
    for lo, hi, label in OPP_RANK_BRACKETS:
        bucket = [s for s in samples
                  if (s.get('features') or {}).get('opp_rank') is not None
                  and lo <= s['features']['opp_rank'] <= hi]
        maybe_add(f'opp_rank_{lo}_{hi}', bucket, 'opp_rank',
                   f'vs {label}: {{delta:+.1f}} pts (n={{n}})')

    # 3. Per park factor bracket
    for lo, hi, label in PARK_BRACKETS:
        bucket = [s for s in samples
                  if (s.get('features') or {}).get('park_factor') is not None
                  and lo <= s['features']['park_factor'] < hi]
        maybe_add(f'park_{lo}_{hi}', bucket, 'park',
                   f'in {label}: {{delta:+.1f}} pts (n={{n}})')

    # 4. Platoon
    for plat in ('edge', 'risk'):
        bucket = [s for s in samples if (s.get('features') or {}).get('platoon') == plat]
        maybe_add(f'platoon_{plat}', bucket, 'platoon',
                   f'with platoon {plat}: {{delta:+.1f}} pts (n={{n}})')

    # 5. Tag
    for tag in ('ACE', 'SAFE', 'UPSIDE'):
        bucket = [s for s in samples if (s.get('features') or {}).get('tag') == tag]
        maybe_add(f'tag_{tag}', bucket, 'tag',
                   f'{tag}-tagged predictions: {{delta:+.1f}} pts (n={{n}})')

    # 6. Trend
    for trend in ('hot', 'cold'):
        bucket = [s for s in samples if (s.get('features') or {}).get('trend') == trend]
        maybe_add(f'trend_{trend}', bucket, 'trend',
                   f'on {trend} streak: {{delta:+.1f}} pts (n={{n}})')

    # 7. Home/Away
    for ha in ('H', 'A'):
        bucket = [s for s in samples if s.get('home_away') == ha]
        maybe_add(f'home_away_{ha}', bucket, 'home_away',
                   f'{"home" if ha == "H" else "road"} starts: {{delta:+.1f}} pts (n={{n}})')

    # 8. Per-pitcher: requires larger sample and valid variance. Small
    # samples with huge/invalid z-scores are surfaced as ineligible candidates.
    by_pitcher = {}
    for s in samples:
        nm = normalize_name(s.get('name', ''))
        if nm:
            by_pitcher.setdefault(nm, []).append(s)
    for nm, bucket in by_pitcher.items():
        display_name = bucket[-1].get('name', nm)
        maybe_add(
            f'pitcher_{nm}', bucket, 'pitcher',
            f'{display_name} historically {{delta:+.1f}} pts vs prediction (n={{n}})',
            min_abs=0.8,
        )

    # 9. Auto-discover correlations in any numeric feature we have data on.
    #    This is the engine that finds unexpected signals: drop any new feature
    #    into the prediction record and the system quartile-buckets and tests
    #    it for residual bias automatically.
    for fname in NUMERIC_AUTO_BUCKET_FEATURES:
        for bucket, lbl, lo, hi in _auto_bucket_continuous(samples, fname, n_buckets=4):
            key = f'auto_{fname}_{lo:.2f}_{hi:.2f}'
            maybe_add(key, bucket, f'auto:{fname}',
                      f'when {lbl}: {{delta:+.1f}} pts (n={{n}})')

    # Sort candidates (close-to-significant or unsafe) by |z| then |mean|.
    candidates.sort(key=lambda c: (-(abs(c.get('z') or 0)), -(abs(c.get('mean') or 0))))
    return {
        'biases': biases,
        'candidates': candidates[:12],
        'tests_run': test_count,
        'samples': len(samples),
        'sample_selection': learning_stats,
    }


def save_learned_biases(biases):
    if PREVIEW_LOCAL:
        print("  Local preview mode: skipping learned biases write")
        return
    payload = {
        'updated_at': datetime.now().isoformat(timespec='seconds'),
        'count': len(biases),
        'biases': biases,
    }
    try:
        with open(LEARNED_BIASES_PATH, 'w') as f:
            json.dump(payload, f, indent=2, sort_keys=True)
    except Exception as e:
        print(f"  Could not save learned biases: {e}")


def load_learned_biases():
    if not os.path.exists(LEARNED_BIASES_PATH):
        return {}
    try:
        with open(LEARNED_BIASES_PATH) as f:
            data = json.load(f)
        return data.get('biases', {})
    except Exception:
        return {}


def apply_learned_biases(entry, biases, damping=0.6):
    """Look up biases that match this entry's features.
    Returns (total_delta, applied_list).

    Per-pitcher applies at full weight (most specific). Categorical buckets
    (tier/opp_rank/park/platoon/tag/trend/home_away) get damped when more
    than one applies, since they often correlate (e.g., must_start tier and
    ACE tag overlap heavily).
    """
    if not biases:
        return 0.0, []

    applied = []

    # Per-pitcher (full weight)
    pname = normalize_name(entry.get('name', ''))
    pkey = f'pitcher_{pname}'
    if pkey in biases:
        b = dict(biases[pkey])
        b['delta_applied'] = b.get('applied_delta', b.get('mean', 0.0))
        applied.append(b)

    # Categorical buckets — collect all that apply
    bucket_hits = []
    tkey = f"tier_{entry.get('tier')}"
    if tkey in biases:
        bucket_hits.append(biases[tkey])

    rank = entry.get('opp_rank')
    if rank is not None:
        for lo, hi, _ in OPP_RANK_BRACKETS:
            k = f'opp_rank_{lo}_{hi}'
            if k in biases and lo <= rank <= hi:
                bucket_hits.append(biases[k])
                break

    pf = entry.get('park_factor')
    if pf is not None:
        for lo, hi, _ in PARK_BRACKETS:
            k = f'park_{lo}_{hi}'
            if k in biases and lo <= pf < hi:
                bucket_hits.append(biases[k])
                break

    if entry.get('platoon'):
        k = f"platoon_{entry['platoon']}"
        if k in biases:
            bucket_hits.append(biases[k])

    if entry.get('tag'):
        k = f"tag_{entry['tag']}"
        if k in biases:
            bucket_hits.append(biases[k])

    if entry.get('trend'):
        k = f"trend_{entry['trend']}"
        if k in biases:
            bucket_hits.append(biases[k])

    if entry.get('home_away'):
        k = f"home_away_{entry['home_away']}"
        if k in biases:
            bucket_hits.append(biases[k])

    # Damping multiplier: 1.0 if 1 hit, scales down with multiple hits
    if bucket_hits:
        scale = 1.0 if len(bucket_hits) == 1 else damping
        for b in bucket_hits:
            b2 = dict(b)
            base_delta = b.get('applied_delta', b.get('mean', 0.0))
            b2['delta_applied'] = round(base_delta * scale, 2)
            applied.append(b2)

    total = round(sum(b['delta_applied'] for b in applied), 2)
    return total, applied


# =============================================================================
# GITHUB SYNC
# =============================================================================

def _ft_report_paths():
    """Resolve the ft-report repo paths if it exists alongside this script."""
    git_dir = os.path.join(SCRIPT_DIR, 'ft-report')
    engine_dir = os.path.join(git_dir, 'engine')
    if not os.path.isdir(os.path.join(git_dir, '.git')):
        return None, None
    return git_dir, engine_dir


def _clear_stale_git_locks(git_dir):
    """Remove any stale .lock files in .git/. Defensive cleanup so a
    previous timed-out git op doesn't wedge subsequent runs."""
    git_internal = os.path.join(git_dir, '.git')
    if not os.path.isdir(git_internal):
        return
    for fname in ('index.lock', 'HEAD.lock', 'refs/heads/main.lock'):
        path = os.path.join(git_internal, fname)
        if os.path.exists(path):
            try:
                os.remove(path)
            except Exception:
                pass


def _mirror_dir(src, dst):
    """Copy any newer files from src into dst (one-way mirror, no deletes)."""
    import shutil
    if not os.path.isdir(src):
        return 0
    copied = 0
    for root, _, files in os.walk(src):
        rel = os.path.relpath(root, src)
        target = os.path.join(dst, rel) if rel != '.' else dst
        os.makedirs(target, exist_ok=True)
        for fn in files:
            s = os.path.join(root, fn)
            d = os.path.join(target, fn)
            if not os.path.exists(d) or os.path.getmtime(s) > os.path.getmtime(d) + 0.5:
                shutil.copy2(s, d)
                copied += 1
    return copied


def _pull_from_github_repo():
    """At the START of a local run, pull the latest snapshots/cache from
    the cloud so local mirrors whatever Actions wrote since last local run.
    Without this step, local always sees a stale 'previous' snapshot."""
    git_dir, engine_dir = _ft_report_paths()
    if not git_dir:
        return
    try:
        import subprocess
        _clear_stale_git_locks(git_dir)
        # Pull --rebase so a local commit doesn't block fast-forward
        result = subprocess.run(
            ['git', '-C', git_dir, 'pull', '--rebase', '--autostash', '--quiet'],
            capture_output=True, text=True, timeout=120,
        )
        if result.returncode != 0:
            print(f"  GitHub pull skipped: {result.stderr.strip() or 'non-zero exit'}")
            return
        # Mirror cloud cache/snapshots/predictions into local working dirs
        snap_copied = _mirror_dir(os.path.join(engine_dir, 'tracker_snapshots'),
                                  os.path.join(SCRIPT_DIR, 'tracker_snapshots'))
        cache_copied = _mirror_dir(os.path.join(engine_dir, 'streaming_cache'),
                                   os.path.join(SCRIPT_DIR, 'streaming_cache'))
        pred_copied = _mirror_dir(os.path.join(engine_dir, 'predictions'),
                                  os.path.join(SCRIPT_DIR, 'predictions'))
        # Single-file outcome log: pull the cloud version if newer
        import shutil
        for fn in ('predictions_outcomes.jsonl', 'learned_biases.json'):
            cloud_path = os.path.join(engine_dir, fn)
            local_path = os.path.join(SCRIPT_DIR, fn)
            if os.path.exists(cloud_path):
                if (not os.path.exists(local_path) or
                        os.path.getmtime(cloud_path) > os.path.getmtime(local_path) + 0.5):
                    shutil.copy2(cloud_path, local_path)
        if snap_copied or cache_copied or pred_copied:
            print(f"Pulled latest from GitHub: {snap_copied} snapshot(s), "
                  f"{cache_copied} cache file(s), {pred_copied} prediction(s)")
        else:
            print("Pulled latest from GitHub: already up-to-date")
    except Exception as e:
        print(f"  GitHub pull skipped: {e}")


def _push_to_github_repo():
    """At the END of a local run, push cache + snapshots back to the cloud.

    Runtime sync intentionally excludes source code. Normal tracker execution
    should move generated state only; code changes belong to the explicit
    developer commit workflow so a stale sibling checkout can never overwrite
    or downgrade engine/fantasy_tracker.py during a data refresh.
    """
    git_dir, engine_dir = _ft_report_paths()
    if not git_dir:
        return
    try:
        import shutil, subprocess
        _clear_stale_git_locks(git_dir)

        # Mirror generated data only. Do not copy source files during runtime
        # sync; use scripts/safe_commit.sh for intentional code changes.
        _mirror_dir(os.path.join(SCRIPT_DIR, 'tracker_snapshots'),
                    os.path.join(engine_dir, 'tracker_snapshots'))
        _mirror_dir(os.path.join(SCRIPT_DIR, 'streaming_cache'),
                    os.path.join(engine_dir, 'streaming_cache'))
        _mirror_dir(os.path.join(SCRIPT_DIR, 'predictions'),
                    os.path.join(engine_dir, 'predictions'))
        # Remove any legacy per-pitcher prediction dirs that have a matching
        # JSONL sibling (mirror doesn't propagate deletions).
        engine_pred_dir = os.path.join(engine_dir, 'predictions')
        if os.path.isdir(engine_pred_dir):
            for name in os.listdir(engine_pred_dir):
                full = os.path.join(engine_pred_dir, name)
                if os.path.isdir(full) and re.match(r'^\d{4}-\d{2}-\d{2}$', name):
                    if os.path.exists(os.path.join(engine_pred_dir, f'{name}.jsonl')):
                        try:
                            shutil.rmtree(full)
                        except Exception:
                            pass
        # Single-file logs (outcomes + learned biases)
        for fn in ('predictions_outcomes.jsonl', 'learned_biases.json'):
            local_path = os.path.join(SCRIPT_DIR, fn)
            if os.path.exists(local_path):
                shutil.copy2(local_path, os.path.join(engine_dir, fn))

        # Pull --rebase one more time in case Actions committed during our run
        subprocess.run(['git', '-C', git_dir, 'pull', '--rebase', '--autostash', '--quiet'],
                       capture_output=True, timeout=60)

        # Stage generated data only; only include paths that actually exist on disk
        # (predictions_outcomes.jsonl and engine/predictions/ may be absent
        # on a brand-new install).
        candidate_paths = [
            'engine/tracker_snapshots',
            'engine/streaming_cache',
            'engine/predictions',
            'engine/predictions_outcomes.jsonl',
            'engine/learned_biases.json',
        ]
        existing = [p for p in candidate_paths if os.path.exists(os.path.join(git_dir, p))]
        if existing:
            subprocess.run(
                ['git', '-C', git_dir, 'add', *existing],
                check=True, capture_output=True,
            )
        diff = subprocess.run(
            ['git', '-C', git_dir, 'diff', '--staged', '--quiet'],
            capture_output=True,
        )
        if diff.returncode == 0:
            print("\nGitHub sync: nothing changed locally")
            return

        subprocess.run(
            ['git', '-C', git_dir,
             '-c', 'user.email=devz0r@users.noreply.github.com',
             '-c', 'user.name=devz0r',
             'commit', '-m', f'Local run sync {datetime.now().strftime("%Y-%m-%d %H:%M")}'],
            check=True, capture_output=True, timeout=30,
        )
        push = subprocess.run(['git', '-C', git_dir, 'push'],
                              capture_output=True, text=True, timeout=60)
        if push.returncode != 0:
            print(f"\nGitHub push failed: {push.stderr.strip()}")
            return
        print("\nPushed code + data to GitHub ✓")

        # Trigger the cloud workflow so the encrypted index.html refreshes
        # using the data we just pushed (instead of waiting for the next cron).
        gh = shutil.which('gh')
        if gh:
            trig = subprocess.run(
                [gh, 'workflow', 'run', 'deploy.yml', '--repo', 'devz0r/ft-report'],
                capture_output=True, text=True, timeout=30,
            )
            if trig.returncode == 0:
                print("Triggered cloud rebuild — devz0r.github.io will refresh in ~1-2 min")
            else:
                print(f"Workflow trigger failed: {trig.stderr.strip()}")
    except Exception as e:
        print(f"\nGitHub sync skipped: {e}")


# =============================================================================
# MAIN
# =============================================================================

def main():
    global PREVIEW_LOCAL, OUTPUT_HTML

    parser = argparse.ArgumentParser(description='Fantasy Baseball In-Season Tracker')
    parser.add_argument('--setup', action='store_true', help='Configure ESPN authentication')
    parser.add_argument('--audit-features', action='store_true', help='Audit prediction feature registry/log consistency')
    parser.add_argument('--audit-warehouse', action='store_true', help='Audit DuckDB/Parquet warehouse foundation')
    parser.add_argument('--audit-outcome-duplicates', action='store_true', help='Dry-run audit for duplicate outcome rows')
    parser.add_argument('--audit-probable-dates', action='store_true', help='Read-only audit for stale/conflicting probable pitcher dates')
    parser.add_argument('--dedupe-outcomes', action='store_true', help='Backup and rewrite predictions_outcomes.jsonl without stable duplicates')
    parser.add_argument('--backfill-warehouse-outcomes', action='store_true', help='Backfill outcome Parquet files from predictions_outcomes.jsonl')
    parser.add_argument('--backfill-warehouse-features', action='store_true', help='Backfill prediction and SP feature Parquet files from prediction JSONL')
    parser.add_argument('--backfill-warehouse-features-from-archive', action='store_true', help='Backfill prediction and SP feature Parquet from predictions_archive plus current prediction JSONL')
    parser.add_argument('--analyze-feature-errors', action='store_true', help='Read-only exploratory feature/error analysis from warehouse training rows')
    parser.add_argument('--analyze-model-baselines', action='store_true', help='Read-only warehouse comparison of current predictions against baseline layers')
    parser.add_argument('--analyze-start-sit-quality', action='store_true', help='Read-only start/sit decision-quality analysis from labeled starts')
    parser.add_argument('--analyze-start-sit-misses', action='store_true', help='Read-only explanation analysis for start/sit decision misses')
    parser.add_argument('--analyze-start-sit-policy-backtest', action='store_true', help='Read-only comparison of alternate start/sit decision policies')
    parser.add_argument('--analyze-risk-guard-weights', action='store_true', help='Read-only comparison of weighted risk-guard overlays')
    parser.add_argument('--daily-decision-audit', action='store_true', help='Read-only daily pitching decision summary from existing prediction logs')
    parser.add_argument('--matchup-snapshot', action='store_true', help='Read-only ESPN head-to-head matchup snapshot')
    parser.add_argument('--matchup-actions', action='store_true', help='Read-only matchup action recommendations from existing data')
    parser.add_argument('--matchup-edge', action='store_true', help='Read-only rough current H2H matchup edge summary')
    parser.add_argument('--hitter-decisions', action='store_true', help='Read-only hitter lineup/FA decisions from existing roster and RoS data')
    parser.add_argument('--hitter-context', action='store_true', help='Read-only logged hitter daily context coverage')
    parser.add_argument('--analyze-hitter-decision-context', action='store_true', help='Read-only hitter decision context reliability analysis')
    parser.add_argument('--analyze-hitter-context-coverage', action='store_true', help='Read-only hitter context coverage and confidence audit')
    parser.add_argument('--audit-hitter-decision-log', action='store_true', help='Read-only audit of generated hitter decision logs')
    parser.add_argument('--refresh-hitter-lineups', action='store_true', help='Refresh local MLB posted-lineup cache for hitter decisions')
    parser.add_argument('--debug-matchup-payload', action='store_true', help='Read-only compact ESPN matchup payload diagnostic')
    parser.add_argument('--explain-pitcher-schedule', metavar='PITCHER', help='Read-only probable-date diagnostic for one pitcher')
    parser.add_argument('--preview-local', action='store_true', help='Write a local preview report without mutating tracked generated files')
    parser.add_argument('--fast-preview', action='store_true', help='Generate a local preview from cached artifacts without live refreshes')
    parser.add_argument('--timing', action='store_true', help='Print runtime timing summary (normal runs print it by default)')
    parser.add_argument('--top', type=int, default=30, help='Show top N in console')
    args = parser.parse_args()

    timings = []

    def timed(label, fn, *fn_args, **fn_kwargs):
        started = time.perf_counter()
        try:
            return fn(*fn_args, **fn_kwargs)
        finally:
            timings.append((label, time.perf_counter() - started))

    def print_timing_summary():
        if not timings:
            return
        print("\nRuntime timing summary")
        print("-" * 60)
        for label, elapsed in timings:
            print(f"  {label:<34s} {elapsed:>7.2f}s")
        print(f"  {'Total timed runtime':<34s} {sum(t for _, t in timings):>7.2f}s")

    if args.audit_features:
        audit_features()
        return

    if args.audit_warehouse:
        audit_warehouse()
        return

    if args.audit_outcome_duplicates:
        audit_outcome_duplicates()
        return

    if args.audit_probable_dates:
        audit_probable_dates()
        return

    if args.explain_pitcher_schedule:
        explain_pitcher_schedule(args.explain_pitcher_schedule)
        return

    if args.dedupe_outcomes:
        dedupe_outcomes()
        return

    if args.backfill_warehouse_outcomes:
        backfill_warehouse_outcomes()
        return

    if args.backfill_warehouse_features:
        backfill_warehouse_features()
        return

    if args.backfill_warehouse_features_from_archive:
        backfill_warehouse_features_from_archive()
        return

    if args.analyze_feature_errors:
        analyze_feature_errors()
        return

    if args.analyze_model_baselines:
        analyze_model_baselines()
        return

    if args.analyze_start_sit_quality:
        analyze_start_sit_quality()
        return

    if args.analyze_start_sit_misses:
        analyze_start_sit_misses()
        return

    if args.analyze_start_sit_policy_backtest:
        analyze_start_sit_policy_backtest()
        return

    if args.analyze_risk_guard_weights:
        analyze_risk_guard_weights()
        return

    if args.daily_decision_audit:
        daily_decision_audit()
        return

    if args.matchup_snapshot:
        matchup_snapshot()
        return

    if args.debug_matchup_payload:
        debug_matchup_payload()
        return

    if args.matchup_actions:
        matchup_actions()
        return

    if args.matchup_edge:
        matchup_edge()
        return

    if args.hitter_decisions:
        hitter_decisions()
        return

    if args.hitter_context:
        hitter_context()
        return

    if args.analyze_hitter_decision_context:
        analyze_hitter_decision_context()
        return

    if args.analyze_hitter_context_coverage:
        analyze_hitter_context_coverage()
        return

    if args.audit_hitter_decision_log:
        audit_hitter_decision_log()
        return

    if args.refresh_hitter_lineups:
        refresh_hitter_lineups()
        return

    if args.setup:
        run_setup()
        return

    if args.preview_local or args.fast_preview:
        PREVIEW_LOCAL = True
        os.makedirs(LOCAL_PREVIEW_DIR, exist_ok=True)
        OUTPUT_HTML = os.path.join(LOCAL_PREVIEW_DIR, "tracker_report.html")
        print("Local preview mode: no tracked generated files will be written.")
        if args.fast_preview:
            print("Fast preview mode: using cached/local artifacts only.")
    else:
        # Sync down freshest cache/snapshots from cloud before reading anything,
        # so local always works against the same state Actions sees.
        timed("GitHub sync: pull", _pull_from_github_repo)

    if args.fast_preview:
        latest_snapshot = timed("fast preview: load latest snapshot", load_latest_snapshot)
        if not latest_snapshot:
            print("Fast preview failed: no tracker snapshot is available.")
            print_timing_summary()
            return
        snapshot_date = latest_snapshot.get('date') or date.today().isoformat()
        players_list = latest_snapshot.get('players') or []
        print(f"Fast preview: using tracker snapshot {snapshot_date} ({len(players_list)} players)")
        if os.path.exists(os.path.join(SCRIPT_DIR, 'espn_players.json')):
            print("Fast preview: using cached ESPN players from snapshot/match data")
        fast_learned_biases = {}
        if os.path.exists(LEARNED_BIASES_PATH):
            fast_learned_biases = timed("fast preview: load learned biases", load_learned_biases)
            print("Fast preview: using existing learned biases")
        else:
            print("Fast preview: no learned_biases.json found; skipping recompute")

        deltas, prev_date = {}, None
        cum_deltas, oldest_date = {}, None
        print("Fast preview: skipping snapshot delta recomputation")

        streaming_data, prediction_log_range = timed("fast preview: load prediction logs", load_prediction_logs_for_fast_preview)
        print(f"Fast preview: using existing prediction logs ({len(streaming_data)} streaming rows)")
        print(f"Fast preview: prediction log date range {prediction_log_range or 'unknown'}")
        cal = {
            'note': (
                'Fast preview skips detailed accuracy recalculation for speed. '
                'Run --preview-local or the normal tracker for the full Accuracy tab.'
            )
        }
        print("Fast preview: skipping detailed calibration recalculation")
        banner_meta = [f"Snapshot: {snapshot_date}"]
        if prediction_log_range:
            banner_meta.append(f"Prediction logs: {prediction_log_range}")
        fast_hitter_decisions = build_hitter_decision_summary(
            snapshot_date,
            players_list=players_list,
            matchup_snapshot_data=None,
            prediction_records=streaming_data,
            allow_live_snapshot=False,
        )
        fast_preview_banner = (
            '<div class="preview-banner"><b>FAST PREVIEW:</b> using cached prediction logs and snapshots. '
            'This is not a fresh data refresh. Use <code>--preview-local</code> for a fresh local refresh, '
            'or a normal run for a production update.'
            f'<div class="meta">{" &bull; ".join(banner_meta)}</div></div>'
        )
        timed(
            "HTML generation",
            generate_tracker_html,
            players_list, deltas, prev_date, snapshot_date, None,
            streaming_data, cum_deltas, oldest_date,
            global_emerging=set(),
            hold_asof_label=f"cached preview through {snapshot_date}",
            calibration=cal,
            learned_candidates=[],
            learned_biases_override=fast_learned_biases,
            feature_log_status_override='Fast preview: feature-log status not refreshed.',
            matchup_snapshot_summary={
                'available': False,
                'error': 'Fast preview uses cached report artifacts and does not refresh ESPN matchup data.',
            },
            matchup_action_summary={
                'date': snapshot_date,
                'items': [],
                'count': 0,
                'notes': ['Run --preview-local or a normal report for fresh matchup actions.'],
            },
            hitter_decision_summary=fast_hitter_decisions,
            matchup_edge_summary={
                'available': False,
                'date': snapshot_date,
                'label': 'High uncertainty',
                'confidence': 'low',
                'error': 'Fast preview uses cached artifacts and does not refresh ESPN matchup edge data.',
                'recommendations': ['Run --preview-local or a normal report for fresh matchup edge.'],
            },
            skip_unchanged_write=True,
            top_banner_html=fast_preview_banner,
        )
        print("\nDone!")
        print(f"\nOpen {OUTPUT_HTML} to review the local preview.")
        print("GitHub sync skipped in fast preview mode.")
        print_timing_summary()
        return

    # Catch up on outcomes for past predictions (yesterday's starts, etc.)
    # before we make new predictions, so calibration uses the freshest data.
    if PREVIEW_LOCAL:
        print("  Local preview mode: skipping pending-outcome processing")
    else:
        try:
            new_outcomes = timed("pending outcomes", process_pending_outcomes)
            if new_outcomes:
                print(f"Joined {new_outcomes} prediction(s) with their actual outcomes")
        except Exception as e:
            print(f"  Outcome processing failed: {e}")

    # Recompute learned biases from the (possibly updated) outcomes log so
    # this run's predictions get the freshest correction layer.
    learned_biases = {}
    learned_candidates = []
    learning_sample_summary = None
    try:
        result = timed("learned biases", compute_learned_biases)
        if isinstance(result, dict) and 'biases' in result:
            learned_biases = result.get('biases', {}) or {}
            learned_candidates = result.get('candidates', []) or []
            learning_sample_summary = result.get('sample_selection')
            tests = result.get('tests_run', 0)
            n_samples = result.get('samples', 0)
            print(f"Bias scan: {n_samples} outcomes, {tests} buckets tested, "
                  f"{len(learned_biases)} significant, {len(learned_candidates)} near-threshold")
            # Always overwrite the saved biases with the freshest scan — if
            # recompute returns empty, we want predictions to NOT use stale
            # corrections from old/looser thresholds.
            save_learned_biases(learned_biases)
            def fmt_z(rec):
                z = rec.get('z')
                return f'{z:.2f}' if isinstance(z, (int, float)) and math.isfinite(z) else 'invalid'
            for k, b in sorted(learned_biases.items(),
                               key=lambda kv: -abs(kv[1].get('applied_delta', kv[1].get('mean', 0))))[:6]:
                print(f"    [active]    {b.get('label', k)}  (z={fmt_z(b)})")
            for c in learned_candidates[:4]:
                reason = c.get('ineligible_reason')
                suffix = f"; not eligible: {reason}" if reason else ""
                print(f"    [candidate] {c.get('label', '')}  (z={fmt_z(c)}{suffix})")
        else:
            # Old return shape (just dict of biases) — support legacy
            learned_biases = result or {}
            if learned_biases:
                save_learned_biases(learned_biases)
    except Exception as e:
        print(f"  Bias detection failed: {e}")
        import traceback
        traceback.print_exc()

    today = date.today().isoformat()

    # Phase 1: Fetch FG RoS data
    print("=" * 60)
    print("PHASE 1: FETCHING RoS PROJECTIONS")
    print("=" * 60)
    batters_raw = timed("FanGraphs RoS fetch: batters", fetch_fg_ros_data, 'bat', 'rthebatx')
    pitchers_raw = timed("FanGraphs RoS fetch: pitchers", fetch_fg_ros_data, 'pit', 'ratcdc')

    # Phase 2: Process and rank
    print("\n" + "=" * 60)
    print("PHASE 2: PROCESSING")
    print("=" * 60)
    def process_rankings_phase():
        batters = process_fg_batters(batters_raw)
        pitchers = process_fg_pitchers(pitchers_raw)
        rankings = create_rankings(batters, pitchers)
        return batters, pitchers, rankings
    batters_df, pitchers_df, rankings_df = timed("RoS processing/rankings", process_rankings_phase)

    # Phase 3: ESPN matching + roster status
    print("\n" + "=" * 60)
    print("PHASE 3: ESPN INTEGRATION")
    print("=" * 60)
    espn_players = timed("ESPN players fetch", fetch_espn_players)
    fg_players = rankings_df.to_dict('records')
    espn_matches, unmatched = timed("ESPN name matching", match_fg_to_espn, fg_players, espn_players)
    print(f"  Matched: {len(espn_matches)}/{len(rankings_df)}")

    config = load_config()
    roster_map = timed("ESPN roster fetch", fetch_espn_rosters, config)
    if roster_map is None:
        print("  No ESPN auth — status will show '?'. Run --setup to configure.")
    else:
        espn_matches = timed("ESPN roster reconciliation", reconcile_with_roster, espn_matches, roster_map, espn_players)

    # Phase 4: Build player list
    def build_player_list_phase():
        out = []
        for _, row in rankings_df.iterrows():
            display_pos = row.get('pitcher_role', row['best_pos']) if row['type'] in ('pitcher', 'two-way') else row['best_pos']
            entry = {
                'rank': int(row['rank']),
                'name': row['name'],
                'positions': row['positions'],
                'displayPos': display_pos,
                'team': row['team'] or '',
                'dollars': round(float(row['dollars']), 1),
                'rpts': round(float(row['rpts']), 1),
                'type': row['type'],
                'fg_id': row.get('fg_id', ''),
            }
            if 'pitcher_role' in row and pd.notna(row.get('pitcher_role')):
                entry['pitcherRole'] = row['pitcher_role']
            if row['name'] in espn_matches:
                entry['espn_id'] = espn_matches[row['name']]['espn_id']
            out.append(entry)
        return out
    players_list = timed("player list build", build_player_list_phase)
    timed("roster/status cache write", save_roster_status_cache, players_list, espn_matches, roster_map)

    # Phase 5: Snapshots and deltas
    print("\n" + "=" * 60)
    print("PHASE 4: TRACKING CHANGES")
    print("=" * 60)
    def snapshot_delta_phase():
        prev = load_previous_snapshot(today)
        daily_deltas, previous_date = compute_deltas(players_list, prev)
        oldest = load_oldest_snapshot()
        cumulative_deltas, oldest_loaded_date = compute_cumulative_deltas(players_list, oldest)
        return prev, daily_deltas, previous_date, oldest, cumulative_deltas, oldest_loaded_date
    prev_snapshot, deltas, prev_date, oldest_snapshot, cum_deltas, oldest_date = timed(
        "snapshot/delta work", snapshot_delta_phase
    )
    # If oldest == previous, cumulative is same as daily — skip the noise
    if oldest_date == prev_date:
        cum_deltas, oldest_date = {}, None
    if prev_date:
        movers = sum(1 for d in deltas.values() if abs(d.get('dollar_change', 0)) > 0.5)
        print(f"  Comparing to {prev_date}: {movers} significant movers")
        if oldest_date:
            trending = sum(1 for p in players_list
                          if cum_deltas.get(p.get('fg_id') or p['name'], {}).get('total_dollar_change', 0) > 1.0
                          and p.get('dollars', 0) >= -5)
            print(f"  Cumulative since {oldest_date}: {trending} trending up (>$1)")
    else:
        print("  No previous snapshot — this is the baseline")
    timed("snapshot write", save_snapshot, players_list, today)

    # Phase 6: Console output
    print(f"\n{'='*90}")
    print(f"TOP {args.top} PLAYERS (RoS)")
    print(f"{'='*90}")
    print(f"{'Rank':>4s}  {'Name':<28s} {'Pos':>4s} {'Team':<5s} {'$Value':>7s} {'$Chg':>6s} {'Status':<12s}")
    print(f"{'-'*4:>4s}  {'-'*28:<28s} {'-'*4:>4s} {'-'*5:<5s} {'-'*7:>7s} {'-'*6:>6s} {'-'*12:<12s}")

    for p in players_list[:args.top]:
        key = p.get('fg_id') or p['name']
        delta = deltas.get(key, {})
        chg = delta.get('dollar_change')
        chg_str = f"{chg:+.1f}" if chg is not None else "--"
        espn_id = p.get('espn_id')
        if roster_map is None:
            status = '?'
        elif espn_id and espn_id in roster_map:
            info = roster_map[espn_id]
            status = 'MY ROSTER' if info['team_id'] == ESPN_TEAM_ID else info['team_name'][:12]
        else:
            status = 'FA'
        print(f"{p['rank']:>4d}  {p['name']:<28s} {p['displayPos']:>4s} {p['team']:<5s} "
              f"${p['dollars']:>5.1f} {chg_str:>6s} {status:<12s}")

    # Phase 5: Streaming Pitchers
    streaming_data = []
    global_emerging = set()
    espn_probables = {}
    today_lines = {}
    yesterday_lines = {}
    recent_completed_sets = []
    try:
        print("\n" + "=" * 60)
        print("PHASE 5: STREAMING PITCHERS")
        print("=" * 60)
        week_start, week_end = get_streaming_window()
        print(f"  Streaming window: {week_start} to {week_end}")

        fg_proj = timed("stream fetch: FG pitcher projections", fetch_fg_pitcher_projections)
        recent_form = timed("stream fetch: FG recent form", fetch_fg_recent_form)
        # Snapshot the raw (pre-blend) FG L14D so tomorrow's run can detect
        # whether FG has absorbed today's games — prevents double-counting
        # when we blend today's completed starts on subsequent runs.
        timed("stream cache: save FG recent raw", save_recent_raw_snapshot, recent_form)
        prior_day_recent = timed("stream cache: load prior recent", load_prior_day_recent_snapshot)
        today_lines = timed("stream fetch: today's completed starts", fetch_todays_completed_starts)
        yesterday_iso = (date.today() - timedelta(days=1)).isoformat()
        yesterday_lines = timed(
            "stream fetch: yesterday's completed starts",
            fetch_completed_starts_for_date,
            yesterday_iso,
            False,
        )
        recent_completed_sets = [
            (date.today().isoformat(), today_lines),
            (yesterday_iso, yesterday_lines),
        ]
        for offset in (2, 3):
            prior_iso = (date.today() - timedelta(days=offset)).isoformat()
            prior_lines = timed(
                f"stream fetch: completed starts {offset}d ago",
                fetch_completed_starts_for_date,
                prior_iso,
                False,
            )
            recent_completed_sets.append((prior_iso, prior_lines))
        timed("stream blend: today's starts", blend_today_into_recent, recent_form, today_lines, baseline_recent=prior_day_recent)
        schedule = timed("stream fetch: MLB schedule", fetch_weekly_schedule, week_start, week_end)
        espn_probables = timed("stream fetch: ESPN probables", fetch_espn_probables, week_start, week_end)
        projected_team_ops = timed("stream fetch: FG team batting", fetch_fg_projected_team_batting)
        team_offense, league_avg_ops = timed("stream fetch: team offense", fetch_team_offense, projected_team_ops)
        team_hand = timed("stream fetch: team handedness", fetch_team_handedness)

        # Collect MLB IDs for probable pitchers to fetch details
        mlb_ids = set()
        pitcher_ids_by_name = {}
        for g in schedule:
            mid = g.get('pitcher_mlb_id')
            if mid:
                mlb_ids.add(mid)
                pname = normalize_name(g.get('pitcher_name', ''))
                if pname:
                    pitcher_ids_by_name[pname] = mid
        pitcher_ids_by_name = augment_workload_pitcher_ids(
            pitcher_ids_by_name,
            fg_proj,
            espn_probables=espn_probables,
            roster_map=roster_map,
            espn_matches=espn_matches,
        )
        mlb_ids.update(pid for pid in pitcher_ids_by_name.values() if pid)
        pitcher_details = timed("stream fetch: pitcher details", fetch_pitcher_details, list(mlb_ids))
        savant_data = timed("stream fetch: Savant arsenal", fetch_savant_pitch_arsenal)
        # Phase 2 enrichment: more data sources for the auto-learning engine
        savant_advanced = timed("stream fetch: Savant advanced", fetch_savant_advanced_pitcher_stats)
        fg_pitching_plus = timed("stream fetch: FG pitching plus", fetch_fg_pitching_plus)
        team_bullpens = timed("stream fetch: team bullpens", fetch_team_bullpens)
        pitcher_workload = timed(
            "stream build: workload features",
            compute_pitcher_workload,
            PREDICTIONS_DIR,
            OUTCOMES_LOG,
            pitcher_ids_by_name,
        )
        il_hitters, il_returns = timed("stream fetch: team IL hitters", fetch_team_il_hitters, players_list)

        # Build a global emerging/HOLD map for ALL FA + rostered SPs based on recent form,
        # not just those with upcoming starts. This catches pitchers who just had a great
        # start but won't pitch again in the streaming window.
        global_emerging = timed(
            "stream build: global HOLD map",
            build_global_emerging_map,
            fg_proj, recent_form, roster_map, espn_matches, roster_map or {}
        )
        print(f"  Global HOLD candidates: {len(global_emerging)} pitchers")

        streaming_data = timed(
            "streaming pitcher build",
            build_streaming_data,
            schedule, fg_proj, recent_form, team_offense,
            league_avg_ops, team_hand, pitcher_details,
            roster_map, espn_matches, savant_data,
            team_il_hitters=il_hitters,
            team_il_returns=il_returns,
            global_emerging=global_emerging,
            espn_probables=espn_probables,
            learned_biases=learned_biases,
            savant_advanced=savant_advanced,
            fg_pitching_plus=fg_pitching_plus,
            team_bullpens=team_bullpens,
            pitcher_workload=pitcher_workload,
            recent_completed_starts={
                **_recent_logged_start_evidence_from_outcomes(
                    OUTCOMES_LOG,
                    [d for d, _lines in recent_completed_sets],
                ),
                **_recent_prediction_start_evidence([date.today().isoformat(), yesterday_iso]),
                **_recent_completed_starts_map(*recent_completed_sets),
            },
        )
        fa_count = sum(1 for s in streaming_data if s.get('status') == 'FA' and not s.get('tbd'))
        mine_count = sum(1 for s in streaming_data if s.get('status') == 'MY ROSTER')
        tbd_count = sum(1 for s in streaming_data if s.get('tbd'))
        print(f"  Streaming: {fa_count} FA options, {mine_count} of your starters, {tbd_count} TBD slots")
    except Exception as e:
        print(f"  Streaming data failed: {e}")
        import traceback
        traceback.print_exc()

    # Phase 5.5: Calibration summary
    cal = None
    try:
        cal = timed("calibration summary", calibration_stats, window_days=30)
        if cal:
            print("\n" + "=" * 60)
            print(f"PREDICTION ACCURACY (last {cal['window_days']}d, n={cal['n']})")
            print("=" * 60)
            bias_dir = 'underpredicting' if cal['bias'] > 0 else 'overpredicting'
            print(f"  MAE:  {cal['mae']:.2f} pts  |  RMSE: {cal['rmse']:.2f}  |  Bias: {cal['bias']:+.2f} ({bias_dir})")
            print("  Per-tier:")
            for tier in ('must_start', 'start', 'borderline', 'avoid'):
                ts = cal['by_tier'].get(tier)
                if not ts:
                    continue
                print(f"    {tier:11s} n={ts['count']:3d}  predicted {ts['mean_predicted']:>5.1f}  actual {ts['mean_actual']:>5.1f}  ({ts['mean_residual']:+.1f})")
    except Exception as e:
        print(f"  Calibration summary failed: {e}")

    # Phase 6: Generate HTML
    print()
    if today_lines:
        hold_asof_label = date.today().strftime('%b %-d') + f" (incl. {len(today_lines)} games finished today)"
    else:
        hold_asof_label = (date.today() - timedelta(days=1)).strftime('%b %-d')
    timed(
        "HTML generation",
        generate_tracker_html,
        players_list, deltas, prev_date, today, roster_map,
        streaming_data, cum_deltas, oldest_date,
        global_emerging=global_emerging,
        hold_asof_label=hold_asof_label,
        calibration=cal,
        learned_candidates=learned_candidates,
        learning_sample_summary=learning_sample_summary,
        team_handedness_context=team_hand,
    )

    print("\nDone!")
    if PREVIEW_LOCAL:
        print(f"\nOpen {OUTPUT_HTML} to review the local preview.")
        print("GitHub sync skipped in local preview mode.")
        print_timing_summary()
        return

    print(f"\nOpen tracker_report.html to review movements and free agents.")

    # Push code + fresh cache + new snapshot back to GitHub, and trigger
    # the cloud workflow so the public site reflects this run.
    timed("GitHub sync: push", _push_to_github_repo)
    print_timing_summary()


if __name__ == '__main__':
    main()
