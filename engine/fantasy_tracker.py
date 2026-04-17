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
import argparse
from datetime import datetime, date, timedelta
from concurrent.futures import ThreadPoolExecutor, as_completed

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

NAME_OVERRIDES = {}


# =============================================================================
# NAME MATCHING (shared logic with draft ranker)
# =============================================================================

def normalize_name(name):
    if not name:
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
        fg_name = fg['name']
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
    os.makedirs(STREAMING_CACHE_DIR, exist_ok=True)
    filepath = os.path.join(STREAMING_CACHE_DIR, filename)
    with open(filepath, 'w') as f:
        json.dump(data, f, indent=2)


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

            base = {
                'date': game_date, 'day': day_label,
                'game_time': game.get('gameDate', ''),
            }

            if home_pp:
                games.append({
                    **base,
                    'pitcher_name': home_pp.get('fullName', ''),
                    'pitcher_mlb_id': home_pp['id'],
                    'pitcher_team': home_team,
                    'opponent': away_team,
                    'home_away': 'H',
                })
            else:
                games.append({**base, 'pitcher_name': None, 'pitcher_team': home_team, 'opponent': away_team, 'home_away': 'H'})

            if away_pp:
                games.append({
                    **base,
                    'pitcher_name': away_pp.get('fullName', ''),
                    'pitcher_mlb_id': away_pp['id'],
                    'pitcher_team': away_team,
                    'opponent': home_team,
                    'home_away': 'A',
                })
            else:
                games.append({**base, 'pitcher_name': None, 'pitcher_team': away_team, 'opponent': home_team, 'home_away': 'A'})

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


def fetch_todays_completed_starts():
    """Pull today's finished starts from MLB Stats API boxscores.

    Returns dict {normalized_name: {'IP','ER','BB','K','H','team'}} so we can
    blend into FG's L14D numbers before the HOLD assessment runs. This is what
    lets you catch today's good/bad starts before FG's overnight update.
    """
    today_iso = date.today().isoformat()
    print(f"  Fetching today's completed starts ({today_iso})...")
    url = f"https://statsapi.mlb.com/api/v1/schedule?sportId=1&date={today_iso}"
    try:
        resp = requests.get(url, timeout=20)
        resp.raise_for_status()
        data = resp.json()
    except Exception as e:
        print(f"    Schedule fetch failed: {e}")
        return {}

    final_game_pks = []
    for dt in data.get('dates', []):
        for g in dt.get('games', []):
            if g.get('status', {}).get('abstractGameState') == 'Final':
                final_game_pks.append(g.get('gamePk'))

    if not final_game_pks:
        print("    0 final games yet today")
        return {}

    def fetch_box(pk):
        try:
            r = requests.get(f"https://statsapi.mlb.com/api/v1/game/{pk}/boxscore", timeout=15)
            r.raise_for_status()
            return r.json()
        except Exception:
            return None

    lines = {}
    with ThreadPoolExecutor(max_workers=8) as ex:
        for box in ex.map(fetch_box, final_game_pks):
            if not box:
                continue
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
                        lines[normalize_name(name)] = {
                            'name': name,
                            'team': team_abbr,
                            'IP': _ip_to_float(stats.get('inningsPitched', 0)),
                            'ER': stats.get('earnedRuns', 0) or 0,
                            'BB': stats.get('baseOnBalls', 0) or 0,
                            'K': stats.get('strikeOuts', 0) or 0,
                            'H': stats.get('hits', 0) or 0,
                        }
    print(f"    {len(lines)} starters with completed lines today")
    return lines


FG_RECENT_RAW_DIR = os.path.join(SCRIPT_DIR, 'streaming_cache', 'fg_recent_raw')


def save_recent_raw_snapshot(recent):
    """Persist today's raw (pre-blend) FG L14D once per day. Used next day to
    determine whether FG has caught up with today's games (so we don't
    double-count on the blend)."""
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
                r['ERA'] = new_er / new_ip * 9.0
                r['WHIP'] = new_br / new_ip
                r['K9'] = new_k / new_ip * 9.0
                merged = True
        if not merged:
            # First L14D entry for this pitcher (e.g., just returned from minors)
            recent_form[f"{norm}|{team}"] = {
                'IP': ip_t,
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
        for r in roster:
            pos = r.get('position', {}).get('abbreviation', '')
            if pos == 'P':
                continue
            side = r.get('person', {}).get('batSide', {}).get('code', 'R')
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
        }
    except Exception:
        return None


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
    if cached:
        print(f"  Using cached team handedness ({age:.1f}h old)")
        return cached

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
                results[abbr] = data

    _save_streaming_cache('team_handedness.json', results)
    print(f"    {len(results)} teams loaded")
    return results


def _fetch_single_pitcher_details(mlb_id):
    """Fetch career platoon splits + pitch arsenal for one pitcher."""
    try:
        url = f"https://statsapi.mlb.com/api/v1/people/{mlb_id}/stats"
        params = {
            'stats': 'careerStatSplits,pitchArsenal',
            'season': date.today().year,
            'group': 'pitching',
            'sitCodes': 'vl,vr',
        }
        resp = requests.get(url, params=params, timeout=15)
        resp.raise_for_status()
        result = {'mlb_id': mlb_id}

        for stat_group in resp.json().get('stats', []):
            type_name = stat_group.get('type', {}).get('displayName', '')
            if 'Splits' in type_name:
                for split in stat_group.get('splits', []):
                    desc = split.get('split', {}).get('description', '')
                    st = split.get('stat', {})
                    if 'Left' in desc:
                        result['career_vs_l'] = {
                            'ops': st.get('ops', '.700'),
                            'whip': st.get('whip', '1.30'),
                            'k9': st.get('strikeoutsPer9Inn', '8.00'),
                            'ip': st.get('inningsPitched', '0'),
                        }
                    elif 'Right' in desc:
                        result['career_vs_r'] = {
                            'ops': st.get('ops', '.700'),
                            'whip': st.get('whip', '1.30'),
                            'k9': st.get('strikeoutsPer9Inn', '8.00'),
                            'ip': st.get('inningsPitched', '0'),
                        }
            elif 'Arsenal' in type_name:
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

        return result
    except Exception:
        return {'mlb_id': mlb_id}


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
    """Convert a string to float, returning default if empty/invalid."""
    try:
        return float(val) if val and val.strip() else default
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
    ohtani_bat = batters_df[batters_df['name'].str.contains('Ohtani', case=False)]
    ohtani_pit = pitchers_df[pitchers_df['name'].str.contains('Ohtani', case=False)]
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
        pitchers_df = pitchers_df[~pitchers_df['name'].str.contains('Ohtani', case=False)]
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
    """Assess recent form vs projection. Returns 'hot', 'cold', or ''."""
    if not recent:
        return ''
    proj_era = proj.get('ERA', 4.0)
    recent_era = recent.get('ERA', proj_era)
    proj_k9 = proj.get('K9', 8.0)
    recent_k9 = recent.get('K9', proj_k9)
    if recent_era < proj_era - 1.5 or recent_k9 > proj_k9 + 2.0:
        return 'hot'
    if recent_era > proj_era + 1.5:
        return 'cold'
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

    if best_pitch and best_matchup:
        summary = f"Arsenal edge: {best_pitch['grade']} {best_pitch['name'].lower()} vs {opp_team}'s weakness"
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


def build_streaming_data(schedule, fg_proj, recent_form, team_offense,
                         league_avg_ops, team_handedness, pitcher_details,
                         roster_map, espn_matches, savant_data=None,
                         team_il_hitters=None, team_il_returns=None,
                         global_emerging=None, espn_probables=None):
    """Build the full streaming dataset for the week."""
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
    my_sps_by_team = {}  # team_abbr -> list of (fg_name, proj)
    if roster_map:
        for key, proj in fg_proj.items():
            fg_name = proj.get('name', '')
            fg_name_norm = normalize_name(fg_name)
            # Check if this pitcher is on MY ROSTER
            match_entry = None
            if fg_name in espn_matches:
                match_entry = espn_matches[fg_name]
            elif fg_name_norm in espn_matches_norm:
                _, match_entry = espn_matches_norm[fg_name_norm]
            if match_entry:
                eid = match_entry['espn_id']
                if eid in espn_id_to_roster and espn_id_to_roster[eid]['team_id'] == ESPN_TEAM_ID:
                    # Team from projection dict or parsed from the key
                    p_team = proj.get('team', '') or (key.split('|')[-1] if '|' in key else '')
                    if proj.get('GS', 0) >= 5 and p_team:  # Must be a real starter
                        my_sps_by_team.setdefault(p_team, []).append((fg_name, proj, match_entry))

    # Track pitchers already assigned to a date (announced or resolved)
    # Maps pitcher_name -> date string, used to enforce minimum rest (4 days)
    pitcher_start_dates = {}
    for game in schedule:
        if game.get('pitcher_name'):
            pitcher_start_dates[game['pitcher_name']] = game['date']

    streaming = []
    for game in schedule:
        pitcher_name = game.get('pitcher_name')
        if not pitcher_name:
            # TBD slot — first try ESPN probables (often ahead of MLB), then fall
            # back to inferring from user's roster.
            team = game['pitcher_team']
            resolved = False
            if espn_probables:
                esp_name = espn_probables.get((game['date'], team))
                if esp_name:
                    pitcher_name = esp_name
                    game = dict(game, pitcher_name=esp_name)
                    pitcher_start_dates[esp_name] = game['date']
                    resolved = True
            if not resolved and team in my_sps_by_team:
                candidates = my_sps_by_team[team]
                # Filter out pitchers who already have a start in the window
                # (a pitcher can't start twice within 4 days on normal rest)
                game_date = date.fromisoformat(game['date'])
                available = []
                for n, p, m in candidates:
                    prev_date_str = pitcher_start_dates.get(n)
                    if prev_date_str:
                        prev_date = date.fromisoformat(prev_date_str)
                        if abs((game_date - prev_date).days) < 5:
                            continue  # Too close to another start
                    available.append((n, p, m))
                if len(available) == 1:
                    fg_name, proj, match_entry = available[0]
                    pitcher_name = fg_name
                    game = dict(game, pitcher_name=fg_name)
                    pitcher_start_dates[fg_name] = game['date']
                    resolved = True
            if not resolved:
                streaming.append({
                    'date': game['date'], 'day': game['day'],
                    'name': 'TBD', 'team': team,
                    'opponent': game['opponent'], 'home_away': game['home_away'],
                    'tbd': True,
                })
                continue

        pitcher_team = game['pitcher_team']
        norm_key = f"{normalize_name(pitcher_name)}|{pitcher_team}"
        proj = fg_by_name.get(norm_key) or fg_by_name.get(normalize_name(pitcher_name))
        if not proj:
            continue  # Can't score without projections

        # Skip openers/bulk relievers: real starters project for 8+ GS RoS
        proj_gs = proj.get('GS', 0)
        proj_ip = proj.get('IP', 0)
        if proj_gs < 5 or (proj_ip > 0 and proj_ip / max(proj_gs, 1) > 7.5):
            continue

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

        # Only include FA and MY ROSTER
        if status not in ('FA', 'MY ROSTER'):
            continue

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

        streaming.append({
            'date': game['date'], 'day': game['day'],
            'name': fg_name, 'team': pitcher_team,
            'opponent': opp, 'home_away': game['home_away'],
            'pts': round(effective_pts, 1), 'base_pts': round(adj_pts, 1),
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
            'tag': tag,
            'trend': trend,
            'recent_era': round(recent['ERA'], 2) if recent else None,
            'fb_velo': details.get('fb_velo'),
            'pitch_count': details.get('pitch_count', 0),
            'status': status,
            'tbd': False,
            'tier': tier,
            'tier_label': TIER_LABELS.get(tier, ''),
            'pitch_analysis': pitch_analysis,
            'emerging': emerging,
            'opp_il': opp_il,
            'opp_il_returns': opp_il_returns,
        })

    # Sort by date, then by tier, then by pts descending within each tier
    streaming.sort(key=lambda s: (s['date'], TIER_ORDER.get(s.get('tier', 'avoid'), 3), -(s.get('pts') or -999)))
    return streaming


# =============================================================================
# HTML REPORT GENERATION
# =============================================================================

def generate_tracker_html(players_list, deltas, prev_date, snapshot_date, roster_map,
                          streaming_data=None, cum_deltas=None, oldest_date=None,
                          global_emerging=None, hold_asof_label=None):
    from string import Template
    if streaming_data is None:
        streaming_data = []
    if cum_deltas is None:
        cum_deltas = {}

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
</style>
</head>
<body>

<div class="header">
  <h1>Fantasy In-Season Tracker</h1>
  <div class="subtitle">Snapshot: $SNAPSHOT_DATE ($PREV_LABEL) &bull; RoS Projections &bull; THE BAT X RoS (bat) + ATC DC RoS (pit)</div>
  <div class="tab-bar">
    <button class="tab-btn active" data-tab="tracker">RoS Tracker</button>
    <button class="tab-btn" data-tab="streaming">Streaming</button>
  </div>
</div>

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
<div id="streamContent"></div>
</div><!-- end tab-streaming -->

<script>
var PLAYERS = $PLAYERS_JSON;
var STREAMING = $STREAMING_JSON;

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
      html += '<div class="stream-tbd">' + s.team + ' vs ' + s.opponent + ' (' + s.home_away + ') \u2014 probable pitcher TBD</div>';
    });

    html += '</div>';
  });
  container.innerHTML = html;
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

  var matchup = s.home_away === 'H' ? 'vs ' + s.opponent : '@' + s.opponent;

  var h = '<div class="' + cls + '">';
  // Row 1
  h += '<div class="stream-row1">';
  if (isTop) h += '<span class="stream-name"><span class="star">\u2605</span>' + s.name + '</span>';
  else h += '<span class="stream-name">' + s.name + '</span>';
  h += '<span class="stream-team">' + s.team + '</span>';
  h += '<span class="stream-matchup">' + matchup + ' (' + s.home_away + ')</span>';
  h += '<span class="stream-pts ' + ptsCls + '">' + s.pts.toFixed(1) + ' pts</span>';
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
  if (s.vs_l_ops && s.vs_r_ops) h += '<span>\u2022 career vs L: ' + s.vs_l_ops + ' / vs R: ' + s.vs_r_ops + '</span>';
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
  h += '</div>';

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

  h += '</div>';
  return h;
}

function ordinal(n) {
  var s = ['th','st','nd','rd'], v = n % 100;
  return n + (s[(v-20)%10] || s[v] || s[0]);
}

renderStreaming();
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
    )

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
# MAIN
# =============================================================================

def main():
    parser = argparse.ArgumentParser(description='Fantasy Baseball In-Season Tracker')
    parser.add_argument('--setup', action='store_true', help='Configure ESPN authentication')
    parser.add_argument('--top', type=int, default=30, help='Show top N in console')
    args = parser.parse_args()

    if args.setup:
        run_setup()
        return

    today = date.today().isoformat()

    # Phase 1: Fetch FG RoS data
    print("=" * 60)
    print("PHASE 1: FETCHING RoS PROJECTIONS")
    print("=" * 60)
    batters_raw = fetch_fg_ros_data('bat', 'rthebatx')
    pitchers_raw = fetch_fg_ros_data('pit', 'ratcdc')

    # Phase 2: Process and rank
    print("\n" + "=" * 60)
    print("PHASE 2: PROCESSING")
    print("=" * 60)
    batters_df = process_fg_batters(batters_raw)
    pitchers_df = process_fg_pitchers(pitchers_raw)
    rankings_df = create_rankings(batters_df, pitchers_df)

    # Phase 3: ESPN matching + roster status
    print("\n" + "=" * 60)
    print("PHASE 3: ESPN INTEGRATION")
    print("=" * 60)
    espn_players = fetch_espn_players()
    fg_players = rankings_df.to_dict('records')
    espn_matches, unmatched = match_fg_to_espn(fg_players, espn_players)
    print(f"  Matched: {len(espn_matches)}/{len(rankings_df)}")

    config = load_config()
    roster_map = fetch_espn_rosters(config)
    if roster_map is None:
        print("  No ESPN auth — status will show '?'. Run --setup to configure.")
    else:
        espn_matches = reconcile_with_roster(espn_matches, roster_map, espn_players)

    # Phase 4: Build player list
    players_list = []
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
        players_list.append(entry)

    # Phase 5: Snapshots and deltas
    print("\n" + "=" * 60)
    print("PHASE 4: TRACKING CHANGES")
    print("=" * 60)
    prev_snapshot = load_previous_snapshot(today)
    deltas, prev_date = compute_deltas(players_list, prev_snapshot)
    oldest_snapshot = load_oldest_snapshot()
    cum_deltas, oldest_date = compute_cumulative_deltas(players_list, oldest_snapshot)
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
    save_snapshot(players_list, today)

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
    try:
        print("\n" + "=" * 60)
        print("PHASE 5: STREAMING PITCHERS")
        print("=" * 60)
        week_start, week_end = get_streaming_window()
        print(f"  Streaming window: {week_start} to {week_end}")

        fg_proj = fetch_fg_pitcher_projections()
        recent_form = fetch_fg_recent_form()
        # Snapshot the raw (pre-blend) FG L14D so tomorrow's run can detect
        # whether FG has absorbed today's games — prevents double-counting
        # when we blend today's completed starts on subsequent runs.
        save_recent_raw_snapshot(recent_form)
        prior_day_recent = load_prior_day_recent_snapshot()
        today_lines = fetch_todays_completed_starts()
        blend_today_into_recent(recent_form, today_lines, baseline_recent=prior_day_recent)
        schedule = fetch_weekly_schedule(week_start, week_end)
        espn_probables = fetch_espn_probables(week_start, week_end)
        projected_team_ops = fetch_fg_projected_team_batting()
        team_offense, league_avg_ops = fetch_team_offense(projected_team_ops)
        team_hand = fetch_team_handedness()

        # Collect MLB IDs for probable pitchers to fetch details
        mlb_ids = set()
        for g in schedule:
            mid = g.get('pitcher_mlb_id')
            if mid:
                mlb_ids.add(mid)
        pitcher_details = fetch_pitcher_details(list(mlb_ids))
        savant_data = fetch_savant_pitch_arsenal()
        il_hitters, il_returns = fetch_team_il_hitters(players_list)

        # Build a global emerging/HOLD map for ALL FA + rostered SPs based on recent form,
        # not just those with upcoming starts. This catches pitchers who just had a great
        # start but won't pitch again in the streaming window.
        global_emerging = build_global_emerging_map(
            fg_proj, recent_form, roster_map, espn_matches, roster_map or {}
        )
        print(f"  Global HOLD candidates: {len(global_emerging)} pitchers")

        streaming_data = build_streaming_data(
            schedule, fg_proj, recent_form, team_offense,
            league_avg_ops, team_hand, pitcher_details,
            roster_map, espn_matches, savant_data,
            team_il_hitters=il_hitters,
            team_il_returns=il_returns,
            global_emerging=global_emerging,
            espn_probables=espn_probables,
        )
        fa_count = sum(1 for s in streaming_data if s.get('status') == 'FA' and not s.get('tbd'))
        mine_count = sum(1 for s in streaming_data if s.get('status') == 'MY ROSTER')
        tbd_count = sum(1 for s in streaming_data if s.get('tbd'))
        print(f"  Streaming: {fa_count} FA options, {mine_count} of your starters, {tbd_count} TBD slots")
    except Exception as e:
        print(f"  Streaming data failed: {e}")
        import traceback
        traceback.print_exc()

    # Phase 6: Generate HTML
    print()
    if today_lines:
        hold_asof_label = date.today().strftime('%b %-d') + f" (incl. {len(today_lines)} games finished today)"
    else:
        hold_asof_label = (date.today() - timedelta(days=1)).strftime('%b %-d')
    generate_tracker_html(players_list, deltas, prev_date, today, roster_map,
                          streaming_data, cum_deltas, oldest_date,
                          global_emerging=global_emerging,
                          hold_asof_label=hold_asof_label)

    print("\nDone!")
    print(f"\nOpen tracker_report.html to review movements and free agents.")


if __name__ == '__main__':
    main()
