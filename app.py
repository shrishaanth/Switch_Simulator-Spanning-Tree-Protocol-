#!/usr/bin/env python3
"""
Packet Tracer-like Layer 2 Switch Simulator
GUI: drag-and-drop topology, per-switch CLI, STP/link visualization, packet animation
"""

import tkinter as tk
from tkinter import ttk, messagebox, filedialog, scrolledtext
import threading
import time
import hashlib
import random
import json
import math
from collections import defaultdict
from datetime import datetime
from enum import Enum

# ─────────────────────────────────────────────────────
#  ENUMS & CONSTANTS  (same engine as original)
# ─────────────────────────────────────────────────────

class PortMode(Enum):
    ACCESS = "access"
    TRUNK  = "trunk"

class PortState(Enum):
    UP   = "up"
    DOWN = "down"

class STPState(Enum):
    BLOCKING   = "BLK"
    LISTENING  = "LIS"
    LEARNING   = "LRN"
    FORWARDING = "FWD"
    DISABLED   = "DIS"

class STPRole(Enum):
    ROOT       = "Root"
    DESIGNATED = "Desg"
    ALTERNATE  = "Altn"
    BACKUP     = "Back"
    DISABLED   = "Disabled"

STP_HELLO_TIME    = 2
STP_MAX_AGE       = 20
STP_FORWARD_DELAY = 15
MAC_AGING_TIME    = 300

# ─────────────────────────────────────────────────────
#  DATA STRUCTURES
# ─────────────────────────────────────────────────────

class MACEntry:
    def __init__(self, mac, port, vlan, entry_type="dynamic"):
        self.mac        = mac
        self.port       = port
        self.vlan       = vlan
        self.entry_type = entry_type
        self.timestamp  = time.time()
        self.hit_count  = 1

    def refresh(self):
        self.timestamp = time.time()
        self.hit_count += 1

    def is_aged_out(self):
        return (self.entry_type == "dynamic" and
                time.time() - self.timestamp > MAC_AGING_TIME)

    def age(self):
        delta = int(time.time() - self.timestamp)
        if delta < 60:   return f"{delta}s"
        if delta < 3600: return f"{delta//60}m{delta%60}s"
        return f"{delta//3600}h{(delta%3600)//60}m"


class VLAN:
    def __init__(self, vid, name=""):
        self.vid    = vid
        self.name   = name if name else f"VLAN{vid:04d}"
        self.active = True


class Interface:
    def __init__(self, name, switch):
        self.name         = name
        self.switch       = switch
        self.mode         = PortMode.ACCESS
        self.access_vlan  = 1
        self.trunk_vlans  = set(range(1, 4095))
        self.native_vlan  = 1
        self.state        = PortState.UP
        self.description  = ""
        self.speed        = "100Mbps"
        self.duplex       = "full"
        self.stp_state    = STPState.FORWARDING
        self.stp_role     = STPRole.DESIGNATED
        self.stp_cost     = 19
        self.stp_priority = 128
        self.connected_to = None   # (sw_hostname, iface_name)
        self.rx_frames    = 0
        self.tx_frames    = 0
        self.rx_errors    = 0
        self.last_change  = time.time()

    def is_forwarding(self):
        return (self.state == PortState.UP and
                self.stp_state == STPState.FORWARDING)

    def link_color(self):
        """For GUI link rendering."""
        if self.state == PortState.DOWN:
            return "#e74c3c"
        if self.stp_state == STPState.BLOCKING:
            return "#f39c12"
        return "#2ecc71"


class STPBridge:
    def __init__(self, switch):
        self.switch          = switch
        self.bridge_priority = 32768
        self.bridge_id       = self._make_bridge_id(32768)
        self.root_id         = self.bridge_id
        self.root_port       = None
        self.root_cost       = 0
        self.topology_change = False

    def _make_bridge_id(self, priority):
        h   = hashlib.md5(self.switch.hostname.encode()).hexdigest()[:12]
        mac = ":".join(h[i:i+2] for i in range(0, 12, 2))
        return f"{priority:05d}.{mac}"

    def set_priority(self, priority):
        self.bridge_priority = priority
        self.bridge_id       = self._make_bridge_id(priority)

    def is_root(self):
        return self.bridge_id == self.root_id

    def recalculate(self):
        up_ports = [i for i in self.switch.interfaces.values()
                    if i.state == PortState.UP]
        if not up_ports:
            return
        if all(i.connected_to is None for i in up_ports):
            self.root_id   = self.bridge_id
            self.root_cost = 0
            self.root_port = None
            for iface in up_ports:
                iface.stp_role  = STPRole.DESIGNATED
                iface.stp_state = STPState.FORWARDING
            return

        best_root = self.bridge_id
        best_cost = 0
        best_port = None

        for iface in up_ports:
            if not iface.connected_to:
                continue
            peer_name, _ = iface.connected_to
            peer_sw = self.switch.topology.get(peer_name)
            if peer_sw and peer_sw.stp.bridge_id < best_root:
                best_root = peer_sw.stp.bridge_id
                best_cost = self.root_cost + iface.stp_cost
                best_port = iface.name

        self.root_id   = best_root
        self.root_cost = best_cost
        self.root_port = best_port

        for iface in up_ports:
            if iface.name == self.root_port:
                iface.stp_role  = STPRole.ROOT
                iface.stp_state = STPState.FORWARDING
            elif iface.connected_to:
                peer_name, _ = iface.connected_to
                peer_sw = self.switch.topology.get(peer_name)
                if peer_sw and peer_sw.stp.bridge_id < self.bridge_id:
                    iface.stp_role  = STPRole.ALTERNATE
                    iface.stp_state = STPState.BLOCKING
                else:
                    iface.stp_role  = STPRole.DESIGNATED
                    iface.stp_state = STPState.FORWARDING
            else:
                iface.stp_role  = STPRole.DESIGNATED
                iface.stp_state = STPState.FORWARDING


# ─────────────────────────────────────────────────────
#  SWITCH ENGINE
# ─────────────────────────────────────────────────────

class Switch:
    NUM_FA = 24
    NUM_GI = 2

    def __init__(self, hostname="Switch"):
        self.hostname    = hostname
        self.vlans       = {1: VLAN(1, "default")}
        self.interfaces  = {}
        self.mac_table   = {}
        self.stp         = STPBridge(self)
        self.topology    = {}
        self.log         = []
        self.enable_mode = False
        self.config_mode = False
        self.iface_mode  = None
        self.vlan_mode   = None
        self._start_time = time.time()
        self._init_interfaces()
        threading.Thread(target=self._aging_loop, daemon=True).start()

    def _init_interfaces(self):
        for i in range(1, self.NUM_FA + 1):
            name = f"FastEthernet0/{i}"
            self.interfaces[name] = Interface(name, self)
        for i in range(1, self.NUM_GI + 1):
            name  = f"GigabitEthernet0/{i}"
            iface = Interface(name, self)
            iface.speed    = "1000Mbps"
            iface.stp_cost = 4
            self.interfaces[name] = iface

    def _aging_loop(self):
        while True:
            time.sleep(30)
            aged = [k for k, v in list(self.mac_table.items()) if v.is_aged_out()]
            for k in aged:
                self._log(f"MAC {k[0]} VLAN {k[1]} aged out from {self.mac_table[k].port}")
                del self.mac_table[k]

    def _log(self, msg):
        ts    = datetime.now().strftime("%H:%M:%S")
        entry = f"[{ts}] {self.hostname}: {msg}"
        self.log.append(entry)
        if len(self.log) > 500:
            self.log = self.log[-400:]

    def _get_iface(self, name):
        nl = name.lower().strip()
        for k in self.interfaces:
            if k.lower() == nl:
                return self.interfaces[k]
            abbrevs = [
                k.lower().replace("fastethernet", "fa"),
                k.lower().replace("fastethernet", "f"),
                k.lower().replace("gigabitethernet", "gi"),
                k.lower().replace("gigabitethernet", "g"),
            ]
            if nl in abbrevs:
                return self.interfaces[k]
        return None

    def _vlan_exists(self, vid):
        return vid in self.vlans

    def _prompt(self):
        base = self.hostname
        if self.iface_mode:  return f"{base}(config-if)# "
        if self.vlan_mode:   return f"{base}(config-vlan)# "
        if self.config_mode: return f"{base}(config)# "
        if self.enable_mode: return f"{base}# "
        return f"{base}> "

    def _unknown(self, cmd):
        return f"% Unknown command: '{cmd}'. Type '?' for help."

    def _uptime(self):
        d = int(time.time() - self._start_time)
        h = d // 3600; m = (d % 3600) // 60; s = d % 60
        return f"{h} hours, {m} minutes, {s} seconds"

    def _bridge_mac(self):
        h = hashlib.md5(self.hostname.encode()).hexdigest()[:12]
        return ":".join(h[i:i+2] for i in range(0, 12, 2))

    def _iface_mac(self, iface):
        h = hashlib.md5((self.hostname + iface.name).encode()).hexdigest()[:12]
        return ":".join(h[i:i+2] for i in range(0, 12, 2))

    def _since(self, ts):
        d = int(time.time() - ts)
        if d < 60:   return f"{d} seconds ago"
        if d < 3600: return f"{d//60} minutes ago"
        return f"{d//3600} hours ago"

    def _fmt_vlan_range(self, vlan_set):
        if not vlan_set:          return "none"
        if len(vlan_set) >= 4094: return "1-4094"
        vlans  = sorted(vlan_set)
        ranges = []
        start  = end = vlans[0]
        for v in vlans[1:]:
            if v == end + 1:
                end = v
            else:
                ranges.append(str(start) if start == end else f"{start}-{end}")
                start = end = v
        ranges.append(str(start) if start == end else f"{start}-{end}")
        return ",".join(ranges)

    def _expand_vlan_range(self, spec):
        result = set()
        try:
            for part in spec.split(","):
                part = part.strip()
                if "-" in part:
                    lo, hi = part.split("-", 1)
                    result.update(range(int(lo), int(hi)+1))
                else:
                    result.add(int(part))
            return result
        except (ValueError, AttributeError):
            return None

    # ── Frame processing ─────────────────────────────

    def process_frame(self, src_mac, dst_mac, vlan, in_port):
        result = {"action": None, "out_ports": [], "dropped": False, "reason": ""}
        iface  = self.interfaces.get(in_port)
        if not iface:
            result["dropped"] = True; result["reason"] = f"Unknown port {in_port}"; return result
        if not iface.is_forwarding():
            result["dropped"] = True; result["reason"] = f"Port {in_port} STP: {iface.stp_state.value}"; return result

        if iface.mode == PortMode.ACCESS:
            vlan = iface.access_vlan
        else:
            if vlan not in iface.trunk_vlans:
                result["dropped"] = True; result["reason"] = f"VLAN {vlan} not allowed on trunk {in_port}"; return result

        iface.rx_frames += 1
        key = (src_mac.upper(), vlan)
        if key in self.mac_table:
            entry = self.mac_table[key]
            if entry.port != in_port:
                self._log(f"MAC move: {src_mac} VLAN {vlan} {entry.port} -> {in_port}")
                entry.port = in_port
            entry.refresh()
        else:
            self.mac_table[key] = MACEntry(src_mac.upper(), in_port, vlan)
            self._log(f"Learned MAC {src_mac} VLAN {vlan} on {in_port}")

        is_broadcast = dst_mac.upper() in ("FF:FF:FF:FF:FF:FF", "BROADCAST")
        is_multicast = dst_mac.upper().startswith("01:")
        dst_key      = (dst_mac.upper(), vlan)

        if is_broadcast or is_multicast:
            result["action"] = "flood"
        elif dst_key in self.mac_table:
            result["action"]    = "forward"
            result["out_ports"] = [self.mac_table[dst_key].port]
        else:
            result["action"] = "flood"

        if result["action"] == "flood":
            for name, port in self.interfaces.items():
                if name == in_port or not port.is_forwarding():
                    continue
                if ((port.mode == PortMode.ACCESS and port.access_vlan == vlan) or
                        (port.mode == PortMode.TRUNK and vlan in port.trunk_vlans)):
                    result["out_ports"].append(name)
                    port.tx_frames += 1
        else:
            for name in result["out_ports"]:
                if name in self.interfaces:
                    self.interfaces[name].tx_frames += 1
        return result

    def send_frame(self, src_mac, dst_mac, vlan, in_port):
        r     = self.process_frame(src_mac, dst_mac, vlan, in_port)
        lines = ["Frame Processing Result", "─" * 42]
        if r["dropped"]:
            lines.append(f"DROPPED: {r['reason']}")
        else:
            lines += [
                f"  Action   : {r['action'].upper()}",
                f"  Src MAC  : {src_mac}",
                f"  Dst MAC  : {dst_mac}",
                f"  VLAN     : {vlan}",
                f"  In Port  : {in_port}",
                f"  Out Ports: {', '.join(r['out_ports']) or 'none'}",
            ]
        return "\n".join(lines)

    # ── Execute dispatcher ────────────────────────────

    def execute(self, cmd):
        cmd = cmd.strip()
        if not cmd: return ""
        tokens = cmd.split(); t0 = tokens[0].lower()

        if self.iface_mode:  return self._exec_iface(cmd, tokens)
        if self.vlan_mode:   return self._exec_vlan_cfg(cmd, tokens)
        if self.config_mode: return self._exec_config(cmd, tokens)

        if t0 == "enable":   self.enable_mode = True;  return ""
        if t0 == "disable":  self.enable_mode = False; return ""
        if t0 in ("exit", "quit", "logout"): return "__EXIT__"
        if t0 in ("?", "help"): return self._help_user()

        if self.enable_mode: return self._exec_enable(cmd, tokens)
        return self._exec_user(cmd, tokens)

    def _exec_user(self, cmd, tokens):
        t0 = tokens[0].lower()
        if t0 == "show": return self._cmd_show(tokens[1:])
        if t0 == "ping": return self._cmd_ping(tokens[1:])
        return self._unknown(cmd)

    def _exec_enable(self, cmd, tokens):
        t0 = tokens[0].lower()
        if t0 == "configure":
            if len(tokens) > 1 and tokens[1].lower() == "terminal":
                self.config_mode = True
                return "Enter configuration commands, one per line.  End with CNTL/Z."
            return "% Incomplete command. Use: configure terminal"
        if t0 == "show":    return self._cmd_show(tokens[1:])
        if t0 == "clear":   return self._cmd_clear(tokens[1:])
        if t0 == "ping":    return self._cmd_ping(tokens[1:])
        if t0 == "reload":  return "% Proceed with reload? [confirm]"
        if t0 in ("write", "copy"): return "Building configuration...\n[OK]"
        if t0 == "debug":   return f"debug {' '.join(tokens[1:])}: enabled (simulated)"
        if t0 in ("exit", "end"): self.enable_mode = False; return ""
        if t0 in ("?", "help"):   return self._help_enable()
        return self._unknown(cmd)

    def _exec_config(self, cmd, tokens):
        t0 = tokens[0].lower()
        if t0 == "hostname" and len(tokens) >= 2:
            self.hostname = tokens[1]
            self.stp.bridge_id = self.stp._make_bridge_id(self.stp.bridge_priority)
            return ""
        if t0 == "interface" and len(tokens) >= 2:
            iface_name = " ".join(tokens[1:])
            iface = self._get_iface(iface_name)
            if not iface: return f"% Interface {iface_name} not found"
            self.iface_mode = iface.name
            return ""
        if t0 == "vlan" and len(tokens) >= 2:
            try:
                vid = int(tokens[1])
            except ValueError:
                return "% Invalid VLAN ID"
            if not (1 <= vid <= 4094): return "% VLAN ID must be 1-4094"
            if vid not in self.vlans:
                self.vlans[vid] = VLAN(vid)
                self._log(f"VLAN {vid} created")
            self.vlan_mode = vid
            return ""
        if t0 == "no" and len(tokens) >= 2:
            sub = tokens[1].lower()
            if sub == "vlan" and len(tokens) >= 3:
                try:
                    vid = int(tokens[2])
                    if vid == 1: return "% Cannot delete VLAN 1"
                    if vid in self.vlans:
                        del self.vlans[vid]
                        self._log(f"VLAN {vid} deleted")
                        return f"VLAN {vid} deleted."
                    return f"% VLAN {vid} does not exist"
                except ValueError:
                    return "% Invalid VLAN ID"
        if t0 == "spanning-tree": return self._cmd_stp_global(tokens[1:])
        if t0 == "mac":           return self._cmd_mac_cfg(tokens[1:])
        if t0 in ("end", "exit"): self.config_mode = False; return ""
        if t0 in ("?", "help"):   return self._help_config()
        return self._unknown(cmd)

    def _exec_iface(self, cmd, tokens):
        t0    = tokens[0].lower()
        iface = self.interfaces[self.iface_mode]
        if t0 == "shutdown":
            iface.state = PortState.DOWN; iface.stp_state = STPState.DISABLED
            iface.last_change = time.time()
            self._log(f"Interface {self.iface_mode} shutdown"); return ""
        if t0 == "no" and len(tokens) >= 2:
            sub = tokens[1].lower()
            if sub == "shutdown":
                iface.state = PortState.UP; iface.stp_state = STPState.FORWARDING
                iface.last_change = time.time()
                self._log(f"Interface {self.iface_mode} enabled"); return ""
            if sub == "description": iface.description = ""; return ""
            if sub == "switchport":  return ""
        if t0 == "description" and len(tokens) >= 2:
            iface.description = " ".join(tokens[1:]); return ""
        if t0 == "switchport":   return self._cmd_switchport(iface, tokens[1:])
        if t0 == "spanning-tree": return self._cmd_stp_iface(iface, tokens[1:])
        if t0 == "speed" and len(tokens) >= 2:
            iface.speed = tokens[1]; return ""
        if t0 == "duplex" and len(tokens) >= 2:
            iface.duplex = tokens[1].lower(); return ""
        if t0 == "interface" and len(tokens) >= 2:
            new_if = self._get_iface(" ".join(tokens[1:]))
            if not new_if: return f"% Interface {' '.join(tokens[1:])} not found"
            self.iface_mode = new_if.name; return ""
        if t0 == "exit": self.iface_mode = None; return ""
        if t0 == "end":  self.iface_mode = None; self.config_mode = False; return ""
        if t0 in ("?", "help"): return self._help_iface()
        return self._unknown(cmd)

    def _cmd_switchport(self, iface, tokens):
        if not tokens: return "% Incomplete command"
        sub = tokens[0].lower()
        if sub == "mode" and len(tokens) >= 2:
            mode = tokens[1].lower()
            if mode == "access": iface.mode = PortMode.ACCESS; return ""
            if mode == "trunk":  iface.mode = PortMode.TRUNK;  return ""
            return f"% Invalid mode: {tokens[1]}"
        if sub == "access" and len(tokens) >= 3:
            if tokens[1].lower() == "vlan":
                try:
                    vid = int(tokens[2])
                    if not self._vlan_exists(vid):
                        self.vlans[vid] = VLAN(vid)
                    iface.access_vlan = vid; return ""
                except ValueError:
                    return "% Invalid VLAN ID"
        if sub == "trunk": return self._cmd_sw_trunk(iface, tokens[1:])
        if sub == "nonegotiate": return ""
        return self._unknown(f"switchport {' '.join(tokens)}")

    def _cmd_sw_trunk(self, iface, tokens):
        if not tokens: return "% Incomplete command"
        sub = tokens[0].lower()
        if sub == "encapsulation": return ""
        if sub == "native" and len(tokens) >= 3:
            try:
                iface.native_vlan = int(tokens[2]); return ""
            except ValueError:
                return "% Invalid VLAN ID"
        if sub == "allowed" and len(tokens) >= 3:
            action   = tokens[2].lower()
            vlan_arg = tokens[3] if len(tokens) >= 4 else action
            if action == "all":  iface.trunk_vlans = set(range(1, 4095)); return ""
            if action == "none": iface.trunk_vlans = set(); return ""
            vlans = self._expand_vlan_range(vlan_arg)
            if vlans is None: return "% Invalid VLAN range"
            if action == "add":    iface.trunk_vlans |= vlans
            elif action == "remove": iface.trunk_vlans -= vlans
            elif action == "except": iface.trunk_vlans = set(range(1, 4095)) - vlans
            else: iface.trunk_vlans = self._expand_vlan_range(action) or vlans
            return ""
        return self._unknown(f"switchport trunk {' '.join(tokens)}")

    def _cmd_stp_global(self, tokens):
        if not tokens: return "% Incomplete command"
        sub = tokens[0].lower()
        if sub == "mode" and len(tokens) >= 2:
            return f"STP mode set to {tokens[1]}."
        if sub == "vlan" and len(tokens) >= 4:
            try:
                vid = int(tokens[1]); prop = tokens[2].lower(); val = int(tokens[3])
                if prop == "priority":
                    if val % 4096 != 0:
                        return "% Priority must be a multiple of 4096"
                    self.stp.set_priority(val); self.stp.recalculate()
                    return f"STP priority set to {val} for VLAN {vid}."
                if prop == "root":
                    self.stp.set_priority(8192); self.stp.recalculate()
                    return f"This switch is the STP root for VLAN {vid}."
            except (ValueError, IndexError):
                return "% Invalid spanning-tree vlan command"
        if sub == "portfast" and len(tokens) >= 2:
            return "PortFast default enabled on all access ports."
        return self._unknown(f"spanning-tree {' '.join(tokens)}")

    def _cmd_stp_iface(self, iface, tokens):
        if not tokens: return "% Incomplete command"
        sub = tokens[0].lower()
        if sub == "portfast":
            iface.stp_state = STPState.FORWARDING; return f"PortFast enabled on {iface.name}."
        if sub == "cost" and len(tokens) >= 2:
            try:
                iface.stp_cost = int(tokens[1]); self.stp.recalculate(); return ""
            except ValueError:
                return "% Invalid cost"
        if sub == "port-priority" and len(tokens) >= 2:
            try:
                iface.stp_priority = int(tokens[1]); self.stp.recalculate(); return ""
            except ValueError:
                return "% Invalid priority"
        if sub in ("bpduguard", "guard"):
            return f"{'BPDU Guard' if sub == 'bpduguard' else 'Root Guard'} enabled on {iface.name}."
        return self._unknown(f"spanning-tree {' '.join(tokens)}")

    def _exec_vlan_cfg(self, cmd, tokens):
        t0  = tokens[0].lower()
        vid = self.vlan_mode
        if t0 == "name" and len(tokens) >= 2:
            self.vlans[vid].name = tokens[1]; return ""
        if t0 == "state" and len(tokens) >= 2:
            self.vlans[vid].active = (tokens[1].lower() != "suspend"); return ""
        if t0 in ("exit", "end"):
            self.vlan_mode = None
            if t0 == "end": self.config_mode = False
            return ""
        return self._unknown(cmd)

    def _cmd_mac_cfg(self, tokens):
        if not tokens: return "% Incomplete command"
        if tokens[0].lower() != "address-table":
            return self._unknown(f"mac {' '.join(tokens)}")
        tokens = tokens[1:]
        if not tokens: return "% Incomplete command"
        sub = tokens[0].lower()
        if sub == "aging-time" and len(tokens) >= 2:
            global MAC_AGING_TIME
            try:
                MAC_AGING_TIME = int(tokens[1]); return f"MAC aging time set to {MAC_AGING_TIME} seconds."
            except ValueError:
                return "% Invalid value"
        if sub == "static" and len(tokens) >= 6:
            mac = tokens[1].upper()
            try:
                vi  = [t.lower() for t in tokens].index("vlan")
                ii  = [t.lower() for t in tokens].index("interface")
                vid = int(tokens[vi+1]); ifn = " ".join(tokens[ii+1:])
                iface = self._get_iface(ifn)
                if not iface: return f"% Interface {ifn} not found"
                self.mac_table[(mac, vid)] = MACEntry(mac, iface.name, vid, "static")
                return f"Static MAC {mac} VLAN {vid} -> {iface.name}."
            except (ValueError, IndexError):
                return "% Usage: mac address-table static <mac> vlan <id> interface <if>"
        return self._unknown(f"mac address-table {' '.join(tokens)}")

    # ── SHOW commands ─────────────────────────────────

    def _cmd_show(self, tokens):
        if not tokens: return "% Incomplete command"
        sub = tokens[0].lower()
        dispatch = {
            "version":           self._show_version,
            "running-config":    self._show_running_config,
            "run":               self._show_running_config,
            "vlan":              lambda: self._show_vlan(tokens[1:]),
            "mac-address-table": lambda: self._show_mac(tokens[1:]),
            "mac":               lambda: self._show_mac(tokens[1:]),
            "spanning-tree":     lambda: self._show_stp(tokens[1:]),
            "cdp":               lambda: self._show_cdp(tokens[1:]),
            "log":               self._show_log,
            "logging":           self._show_log,
            "clock":             self._show_clock,
            "inventory":         self._show_inventory,
        }
        if sub in ("interfaces", "interface"):
            return self._show_interfaces(tokens[1:])
        fn = dispatch.get(sub)
        if fn:        return fn()
        if sub in ("?", "help"): return self._help_enable()
        return self._unknown(f"show {' '.join(tokens)}")

    def _show_version(self):
        return (
            f"Cisco IOS Software Simulator, Version 15.2(4)E9\n"
            f"Copyright (c) 2024 Switch Simulator Project\n\n"
            f"Switch uptime is {self._uptime()}\n\n"
            f"cisco WS-C2960-24TC-L  processor with 65536K bytes of memory.\n"
            f"24 FastEthernet interfaces, 2 GigabitEthernet interfaces\n\n"
            f"Base Ethernet MAC Address : {self._bridge_mac()}\n"
            f"Model number              : WS-C2960-24TC-L\n"
            f"System serial number      : FOC{random.randint(1000,9999)}X{random.randint(100,999)}\n"
        )

    def _show_running_config(self):
        lines = ["Building configuration...\n", "!", f"hostname {self.hostname}", "!",
                 "spanning-tree mode pvst", "spanning-tree extend system-id", "!"]
        for vid, vlan in sorted(self.vlans.items()):
            if vid == 1: continue
            lines += [f"vlan {vid}", f" name {vlan.name}", "!"]
        for name, iface in sorted(self.interfaces.items()):
            changed = (iface.mode == PortMode.TRUNK or iface.access_vlan != 1 or
                       iface.state == PortState.DOWN or bool(iface.description))
            if not changed: continue
            lines.append(f"interface {name}")
            if iface.description: lines.append(f" description {iface.description}")
            if iface.mode == PortMode.ACCESS:
                lines.append(" switchport mode access")
                if iface.access_vlan != 1:
                    lines.append(f" switchport access vlan {iface.access_vlan}")
            else:
                lines.append(" switchport trunk encapsulation dot1q")
                lines.append(" switchport mode trunk")
                if iface.native_vlan != 1:
                    lines.append(f" switchport trunk native vlan {iface.native_vlan}")
                lines.append(f" switchport trunk allowed vlan {self._fmt_vlan_range(iface.trunk_vlans)}")
            if iface.state == PortState.DOWN:
                lines.append(" shutdown")
            lines.append("!")
        lines += ["end", ""]
        return "\n".join(lines)

    def _show_interfaces(self, tokens):
        if tokens:
            arg = tokens[0].lower()
            if arg == "status": return self._show_iface_status()
            iface = self._get_iface(" ".join(tokens))
            if iface: return self._show_single_iface(iface)
            return f"% Interface {' '.join(tokens)} not found"
        return self._show_all_ifaces()

    def _show_single_iface(self, iface):
        state = iface.state.value
        lines = [
            f"{iface.name} is {state}, line protocol is {state}",
        ]
        if iface.description: lines.append(f"  Description: {iface.description}")
        lines += [
            f"  Hardware: {'FastEthernet' if 'Fast' in iface.name else 'GigabitEthernet'},"
            f" address: {self._iface_mac(iface)}",
            f"  MTU 1500 bytes, BW {iface.speed}, Duplex: {iface.duplex}",
            f"  Switchport mode: {iface.mode.value}",
        ]
        if iface.mode == PortMode.ACCESS:
            lines.append(f"  Access VLAN: {iface.access_vlan}")
        else:
            lines.append(f"  Trunk native VLAN: {iface.native_vlan}")
            lines.append(f"  Trunk allowed: {self._fmt_vlan_range(iface.trunk_vlans)}")
        lines += [
            f"  STP role: {iface.stp_role.value}, state: {iface.stp_state.value}, cost: {iface.stp_cost}",
            f"  Input : {iface.rx_frames:>6} frames, {iface.rx_errors} errors",
            f"  Output: {iface.tx_frames:>6} frames",
            f"  Last change: {self._since(iface.last_change)}",
        ]
        if iface.connected_to:
            sw_name, peer_if = iface.connected_to
            lines.append(f"  Connected to: {sw_name} / {peer_if}")
        return "\n".join(lines)

    def _show_all_ifaces(self):
        hdr   = f"{'Interface':<22} {'Status':<8} {'Mode':<8} {'VLAN':<8} {'STP':<5} {'Description'}"
        lines = [hdr, "─" * 70]
        for name, iface in sorted(self.interfaces.items()):
            vlan = (str(iface.access_vlan) if iface.mode == PortMode.ACCESS else "trunk")
            lines.append(
                f"{name:<22} {iface.state.value:<8} {iface.mode.value:<8} "
                f"{vlan:<8} {iface.stp_state.value:<5} {iface.description[:20]}"
            )
        return "\n".join(lines)

    def _show_iface_status(self):
        hdr   = f"{'Port':<22} {'Name':<18} {'Status':<12} {'Vlan':<6} {'Speed':<12} {'Type'}"
        lines = [hdr, "─" * 78]
        for name, iface in sorted(self.interfaces.items()):
            status = "connected" if iface.state == PortState.UP else "notconnect"
            vlan   = (str(iface.access_vlan) if iface.mode == PortMode.ACCESS else "trunk")
            type_  = "10/100BaseTX" if "Fast" in name else "1000BaseSFP"
            lines.append(
                f"{name:<22} {iface.description[:16]:<18} {status:<12} "
                f"{vlan:<6} {iface.speed:<12} {type_}"
            )
        return "\n".join(lines)

    def _show_vlan(self, tokens):
        if tokens:
            arg = tokens[0].lower()
            if arg == "brief": return self._show_vlan_brief()
            if arg == "id" and len(tokens) >= 2:
                try:
                    return self._show_vlan_id(int(tokens[1]))
                except ValueError:
                    return "% Invalid VLAN ID"
        return self._show_vlan_brief()

    def _show_vlan_brief(self):
        hdr   = f"{'VLAN':<6} {'Name':<32} {'Status':<10} {'Ports'}"
        lines = [hdr, "─" * 72]
        for vid, vlan in sorted(self.vlans.items()):
            st    = "active" if vlan.active else "suspend"
            ports = [n.replace("FastEthernet0/","Fa0/").replace("GigabitEthernet0/","Gi0/")
                     for n, i in self.interfaces.items()
                     if i.mode == PortMode.ACCESS and i.access_vlan == vid and i.state == PortState.UP]
            p_str = ", ".join(sorted(ports)[:6])
            if len(ports) > 6: p_str += f", +{len(ports)-6} more"
            lines.append(f"{vid:<6} {vlan.name:<32} {st:<10} {p_str}")
        return "\n".join(lines)

    def _show_vlan_id(self, vid):
        if vid not in self.vlans: return f"% VLAN {vid} not found"
        vlan  = self.vlans[vid]
        ports = [n for n, i in self.interfaces.items()
                 if i.mode == PortMode.ACCESS and i.access_vlan == vid]
        return (
            f"VLAN  Name                  Status    Ports\n"
            f"────  ─────────────────────  ────────  ──────────────────\n"
            f"{vid:<6}{vlan.name:<23}{'active' if vlan.active else 'suspend'}   "
            f"{', '.join(ports)}\n\n"
            f"VLAN Type  SAID       MTU\n"
            f"──── ────── ────────── ─────────────────\n"
            f"{vid:<5}enet   1{vid:06d}  1500"
        )

    def _show_mac(self, tokens):
        entries = list(self.mac_table.values())
        filter_vlan = filter_iface = filter_mac = None
        dynamic_only = static_only = False
        i = 0
        while i < len(tokens):
            t = tokens[i].lower()
            if t == "vlan" and i+1 < len(tokens):
                try: filter_vlan = int(tokens[i+1]); i += 2; continue
                except ValueError: pass
            if t == "interface" and i+1 < len(tokens):
                filter_iface = tokens[i+1]; i += 2; continue
            if t == "address" and i+1 < len(tokens):
                filter_mac = tokens[i+1].upper(); i += 2; continue
            if t == "dynamic": dynamic_only = True
            if t == "static":  static_only  = True
            i += 1
        if filter_vlan:  entries = [e for e in entries if e.vlan == filter_vlan]
        if filter_iface:
            iface = self._get_iface(filter_iface)
            if iface: entries = [e for e in entries if e.port == iface.name]
        if filter_mac:   entries = [e for e in entries if e.mac == filter_mac]
        if dynamic_only: entries = [e for e in entries if e.entry_type == "dynamic"]
        if static_only:  entries = [e for e in entries if e.entry_type == "static"]
        hdr   = f"{'Vlan':<6} {'Mac Address':<20} {'Type':<10} {'Ports':<22} Age"
        lines = ["MAC Address Table", "─" * 65, hdr, "─" * 65]
        if not entries:
            lines.append("  (no entries)")
        else:
            for e in sorted(entries, key=lambda x: (x.vlan, x.mac)):
                port = (e.port.replace("FastEthernet0/","Fa0/").replace("GigabitEthernet0/","Gi0/"))
                lines.append(f"{e.vlan:<6} {e.mac:<20} {e.entry_type:<10} {port:<22} {e.age()}")
        lines.append(f"\nTotal Mac Addresses: {len(entries)}")
        return "\n".join(lines)

    def _show_stp(self, tokens):
        if tokens and tokens[0].lower() == "summary":
            fwd = sum(1 for i in self.interfaces.values() if i.stp_state == STPState.FORWARDING)
            blk = sum(1 for i in self.interfaces.values() if i.stp_state == STPState.BLOCKING)
            return (f"Switch is root: {'YES' if self.stp.is_root() else 'NO'}\n"
                    f"STP mode      : PVST+\n"
                    f"PortFast BPDU guard: Disabled\n\n"
                    f"{'Name':<20} {'Blocking':<10} {'Forwarding':<12} STP Active\n"
                    f"{'─'*52}\n"
                    f"{'VLAN0001':<20} {blk:<10} {fwd:<12} {fwd+blk}")

        root_str = ("This bridge is the root" if self.stp.is_root()
                    else f"Root bridge ID: {self.stp.root_id}")
        lines = [
            f"VLAN0001",
            f"  Spanning tree enabled protocol pvst",
            f"  Root ID    Priority  {self.stp.bridge_priority}",
            f"             Address   {self._bridge_mac()}",
            f"             {root_str}",
            f"",
            f"  Bridge ID  Priority  {self.stp.bridge_priority}",
            f"             Address   {self._bridge_mac()}",
            f"             Hello Time {STP_HELLO_TIME} sec  Max Age {STP_MAX_AGE} sec  Forward Delay {STP_FORWARD_DELAY} sec",
            f"",
            f"{'Interface':<22} {'Role':<8} {'Sts':<6} {'Cost':<8} {'Prio.Nbr':<12} {'Type'}",
            "─" * 65,
        ]
        for name, iface in sorted(self.interfaces.items()):
            if iface.state == PortState.DOWN: continue
            lines.append(
                f"{name:<22} {iface.stp_role.value:<8} {iface.stp_state.value:<6} "
                f"{iface.stp_cost:<8} {iface.stp_priority}.{name[-3:]:<8} P2p"
            )
        return "\n".join(lines)

    def _show_cdp(self, tokens):
        hdr   = f"{'Device ID':<20} {'Local Intrfce':<16} {'Holdtme':<10} {'Capability':<12} {'Port ID'}"
        lines = ["Capability Codes: S - Switch, R - Router\n", hdr, "─" * 65]
        found = False
        for name, iface in self.interfaces.items():
            if not iface.connected_to: continue
            found = True
            sw_name, peer_if = iface.connected_to
            short = name.replace("FastEthernet0/","Fa0/").replace("GigabitEthernet0/","Gi0/")
            peer  = peer_if.replace("FastEthernet0/","Fa0/").replace("GigabitEthernet0/","Gi0/")
            lines.append(f"{sw_name:<20} {short:<16} {'120':<10} {'S':<12} {peer}")
        if not found:
            lines.append("  CDP neighbor table is empty.")
        return "\n".join(lines)

    def _show_log(self):
        if not self.log: return "% Log is empty."
        lines = [f"Syslog (last {min(30,len(self.log))} entries):"]
        for entry in self.log[-30:]:
            lines.append(f"  {entry}")
        return "\n".join(lines)

    def _show_clock(self):
        return f"Current time: {datetime.now().strftime('%H:%M:%S %Z %a %b %d %Y')}"

    def _show_inventory(self):
        sn = f"FOC{random.randint(1000,9999)}X"
        return (f"NAME: \"1\",  DESCR: \"WS-C2960-24TC-L\"\n"
                f"PID: WS-C2960-24TC-L   VID: V07   SN: {sn}\n\n"
                f"NAME: \"Power Supply 1\",  DESCR: \"FRU Power Supply\"\n"
                f"PID: PWR-C2-250WAC   VID: V01   SN: LIT{random.randint(1000,9999)}\n")

    def _cmd_clear(self, tokens):
        if not tokens: return "% Incomplete command"
        sub = tokens[0].lower()
        if sub in ("mac-address-table", "mac"):
            dynamic = [(k,v) for k,v in self.mac_table.items() if v.entry_type == "dynamic"]
            for k, _ in dynamic: del self.mac_table[k]
            self._log(f"Cleared {len(dynamic)} dynamic MAC entries")
            return f"Cleared {len(dynamic)} dynamic MAC address table entries."
        if sub == "counters":
            for iface in self.interfaces.values():
                iface.rx_frames = iface.tx_frames = iface.rx_errors = 0
            return "Interface counters cleared."
        if sub in ("log", "logging"):
            self.log.clear(); return "Log cleared."
        return self._unknown(f"clear {' '.join(tokens)}")

    def _cmd_ping(self, tokens):
        if not tokens: return "% Usage: ping <MAC> [vlan <id>]"
        target = tokens[0].upper(); vlan = 1; tl = [t.lower() for t in tokens]
        if "vlan" in tl:
            try:
                vi = tl.index("vlan"); vlan = int(tokens[vi+1])
            except (ValueError, IndexError):
                pass
        key     = (target, vlan)
        results = ["!" if key in self.mac_table else "." for _ in range(5)]
        line    = "".join(results); success = line.count("!")
        return (f"Sending 5 frames to {target}, VLAN {vlan}\n\n{line}\n\n"
                f"Success rate is {success*20}% ({success}/5)")

    def connect(self, local_if, remote_sw, remote_if):
        li = self._get_iface(local_if); ri = remote_sw._get_iface(remote_if)
        if not li: return f"% Interface {local_if} not found on {self.hostname}"
        if not ri: return f"% Interface {remote_if} not found on {remote_sw.hostname}"
        li.connected_to = (remote_sw.hostname, ri.name)
        ri.connected_to = (self.hostname, li.name)
        self.topology[remote_sw.hostname]     = remote_sw
        remote_sw.topology[self.hostname]     = self
        self.stp.recalculate(); remote_sw.stp.recalculate()
        self._log(f"Connected {li.name} <-> {remote_sw.hostname}/{ri.name}")
        return f"Connected: {self.hostname}/{li.name} <-> {remote_sw.hostname}/{ri.name}"

    def disconnect_iface(self, iface_name):
        iface = self._get_iface(iface_name)
        if not iface or not iface.connected_to: return
        peer_sw_name, peer_if_name = iface.connected_to
        peer_sw = self.topology.get(peer_sw_name)
        if peer_sw:
            peer_iface = peer_sw._get_iface(peer_if_name)
            if peer_iface: peer_iface.connected_to = None
            del peer_sw.topology[self.hostname]
            peer_sw.stp.recalculate()
        iface.connected_to = None
        if peer_sw_name in self.topology:
            del self.topology[peer_sw_name]
        self.stp.recalculate()

    # ── Help texts ────────────────────────────────────

    def _help_user(self):
        return ("User EXEC Commands:\n"
                "  enable           Enter privileged EXEC mode\n"
                "  show             Show running system information\n"
                "  ping <MAC>       Simulate frame lookup\n"
                "  exit / quit      Exit CLI\n"
                "  ?                This help")

    def _help_enable(self):
        return ("Privileged EXEC Commands:\n"
                "  configure terminal     Enter global config mode\n"
                "  show version           System info\n"
                "  show interfaces [<n>]  Interface status\n"
                "  show interfaces status Brief port status\n"
                "  show vlan [brief|id n] VLAN table\n"
                "  show mac-address-table MAC table\n"
                "  show spanning-tree     STP info\n"
                "  show running-config    Active config\n"
                "  show cdp neighbors     CDP neighbors\n"
                "  show log               System log\n"
                "  clear mac-address-table  Clear dynamic MACs\n"
                "  clear counters         Reset port counters\n"
                "  ping <MAC> [vlan <n>]  Probe MAC table\n"
                "  write                  Save config\n"
                "  end / exit             Back to user EXEC\n"
                "  ?                      This help")

    def _help_config(self):
        return ("Global Configuration Commands:\n"
                "  hostname <n>                        Set switch hostname\n"
                "  interface <n>                       Configure an interface\n"
                "  vlan <id>                           Create/configure a VLAN\n"
                "  no vlan <id>                        Delete a VLAN\n"
                "  spanning-tree vlan <id> priority <n>  Set bridge priority\n"
                "  mac address-table aging-time <s>    Set aging timer\n"
                "  end / exit                          Exit config mode\n"
                "  ?                                   This help")

    def _help_iface(self):
        return ("Interface Configuration Commands:\n"
                "  description <text>                  Port description\n"
                "  shutdown / no shutdown              Disable/enable port\n"
                "  switchport mode access|trunk        Set port mode\n"
                "  switchport access vlan <id>         Set access VLAN\n"
                "  switchport trunk encapsulation dot1q\n"
                "  switchport trunk native vlan <id>   Native VLAN\n"
                "  switchport trunk allowed vlan <range|all|none>\n"
                "  spanning-tree portfast              Enable PortFast\n"
                "  spanning-tree cost <n>              Port STP cost\n"
                "  spanning-tree port-priority <n>     Port STP priority\n"
                "  speed <n>   duplex full|half\n"
                "  exit  end\n"
                "  ?                                   This help")

    def to_dict(self):
        """Serialize switch state for save/load."""
        ifaces = {}
        for name, iface in self.interfaces.items():
            ifaces[name] = {
                "mode": iface.mode.value,
                "access_vlan": iface.access_vlan,
                "native_vlan": iface.native_vlan,
                "trunk_vlans": list(iface.trunk_vlans),
                "state": iface.state.value,
                "description": iface.description,
                "speed": iface.speed,
                "duplex": iface.duplex,
                "stp_cost": iface.stp_cost,
                "stp_priority": iface.stp_priority,
                "connected_to": iface.connected_to,
            }
        vlans = {str(vid): {"name": v.name, "active": v.active}
                 for vid, v in self.vlans.items()}
        return {
            "hostname": self.hostname,
            "stp_priority": self.stp.bridge_priority,
            "interfaces": ifaces,
            "vlans": vlans,
        }

    @classmethod
    def from_dict(cls, d):
        sw = cls(d["hostname"])
        sw.stp.set_priority(d.get("stp_priority", 32768))
        # VLANs
        sw.vlans = {}
        for vid_str, vdata in d.get("vlans", {}).items():
            vid = int(vid_str)
            sw.vlans[vid] = VLAN(vid, vdata["name"])
            sw.vlans[vid].active = vdata.get("active", True)
        # Interfaces
        for name, idata in d.get("interfaces", {}).items():
            if name not in sw.interfaces: continue
            iface = sw.interfaces[name]
            iface.mode         = PortMode(idata["mode"])
            iface.access_vlan  = idata["access_vlan"]
            iface.native_vlan  = idata["native_vlan"]
            iface.trunk_vlans  = set(idata["trunk_vlans"])
            iface.state        = PortState(idata["state"])
            iface.description  = idata["description"]
            iface.speed        = idata["speed"]
            iface.duplex       = idata["duplex"]
            iface.stp_cost     = idata["stp_cost"]
            iface.stp_priority = idata["stp_priority"]
            iface.connected_to = (tuple(idata["connected_to"])
                                  if idata.get("connected_to") else None)
        return sw


# ─────────────────────────────────────────────────────
#  GUI APPLICATION
# ─────────────────────────────────────────────────────

COLORS = {
    "bg":          "#1a1a2e",
    "panel":       "#16213e",
    "toolbar":     "#0f3460",
    "canvas_bg":   "#12121f",
    "switch_body": "#1e3a5f",
    "switch_sel":  "#2980b9",
    "switch_root": "#8e44ad",
    "text":        "#ecf0f1",
    "text_dim":    "#7f8c8d",
    "green":       "#2ecc71",
    "orange":      "#f39c12",
    "red":         "#e74c3c",
    "blue":        "#3498db",
    "cyan":        "#1abc9c",
    "yellow":      "#f1c40f",
    "cli_bg":      "#0d0d0d",
    "cli_text":    "#00ff41",
    "cli_prompt":  "#39ff14",
    "cli_error":   "#ff4444",
    "cli_info":    "#4fc3f7",
}


class SwitchNode:
    """Visual representation of a switch on the canvas."""
    W = 90
    H = 60
    ICON_SIZE = 24

    def __init__(self, canvas, switch, x, y):
        self.canvas = canvas
        self.switch = switch
        self.x      = x
        self.y      = y
        self.items  = []
        self.selected = False
        self._draw()

    def _draw(self):
        for item in self.items:
            self.canvas.delete(item)
        self.items = []
        x, y = self.x, self.y

        fill   = COLORS["switch_sel"] if self.selected else (
            COLORS["switch_root"] if self.switch.stp.is_root() else COLORS["switch_body"])
        outline = COLORS["green"] if self.switch.stp.is_root() else COLORS["blue"]

        # Main box with rounded-rect look
        shadow = self.canvas.create_rectangle(x-self.W//2+3, y-self.H//2+3,
                                               x+self.W//2+3, y+self.H//2+3,
                                               fill="#000000", outline="", tags="switch")
        body   = self.canvas.create_rectangle(x-self.W//2, y-self.H//2,
                                               x+self.W//2, y+self.H//2,
                                               fill=fill, outline=outline, width=2,
                                               tags="switch")
        # Switch icon (mini ports)
        iy = y - 6
        for px in range(-3, 4):
            dot = self.canvas.create_rectangle(x + px*10 - 3, iy-4, x + px*10 + 3, iy+4,
                                                fill=COLORS["green"], outline="",
                                                tags="switch")
            self.items.append(dot)

        # Label
        lbl = self.canvas.create_text(x, y+18, text=self.switch.hostname,
                                       fill=COLORS["text"], font=("Consolas", 9, "bold"),
                                       tags="switch")
        # Root crown indicator
        if self.switch.stp.is_root():
            crown = self.canvas.create_text(x, y - self.H//2 - 10, text="♛ ROOT",
                                             fill=COLORS["yellow"], font=("Consolas", 8, "bold"),
                                             tags="switch")
            self.items.append(crown)

        self.items += [shadow, body, lbl]

    def redraw(self):
        self._draw()

    def move(self, dx, dy):
        self.x += dx; self.y += dy
        for item in self.items:
            self.canvas.move(item, dx, dy)

    def hit_test(self, ex, ey):
        return (abs(ex - self.x) <= self.W//2 + 5 and
                abs(ey - self.y) <= self.H//2 + 5)


class LinkLine:
    """Visual link between two switch nodes."""
    def __init__(self, canvas, node1, if1, node2, if2):
        self.canvas = canvas
        self.node1  = node1
        self.if1    = if1
        self.node2  = node2
        self.if2    = if2
        self.line   = None
        self.label1 = None
        self.label2 = None
        self.stp_badge = None
        self._draw()

    def _color(self):
        iface1 = self.node1.switch.interfaces.get(self.if1)
        if not iface1: return COLORS["red"]
        return iface1.link_color()

    def _stp_blocked(self):
        iface1 = self.node1.switch.interfaces.get(self.if1)
        iface2 = self.node2.switch.interfaces.get(self.if2)
        if iface1 and iface1.stp_state == STPState.BLOCKING: return True
        if iface2 and iface2.stp_state == STPState.BLOCKING: return True
        return False

    def _draw(self):
        for item in [self.line, self.label1, self.label2, self.stp_badge]:
            if item: self.canvas.delete(item)

        x1, y1 = self.node1.x, self.node1.y
        x2, y2 = self.node2.x, self.node2.y
        color  = self._color()
        dash   = (6, 4) if self._stp_blocked() else ()

        self.line = self.canvas.create_line(x1, y1, x2, y2, fill=color, width=2.5,
                                             dash=dash, tags="link")
        # Port labels
        mx, my = (x1+x2)/2, (y1+y2)/2
        angle  = math.atan2(y2-y1, x2-x1)
        off    = 15
        lx1 = x1 + math.cos(angle)*off; ly1 = y1 + math.sin(angle)*off
        lx2 = x2 - math.cos(angle)*off; ly2 = y2 - math.sin(angle)*off

        short1 = self.if1.replace("FastEthernet0/","Fa0/").replace("GigabitEthernet0/","Gi0/")
        short2 = self.if2.replace("FastEthernet0/","Fa0/").replace("GigabitEthernet0/","Gi0/")

        self.label1 = self.canvas.create_text(lx1, ly1, text=short1,
                                               fill=COLORS["text_dim"], font=("Consolas",7),
                                               tags="link")
        self.label2 = self.canvas.create_text(lx2, ly2, text=short2,
                                               fill=COLORS["text_dim"], font=("Consolas",7),
                                               tags="link")
        if self._stp_blocked():
            self.stp_badge = self.canvas.create_text(mx, my-10, text="BLK",
                                                      fill=COLORS["orange"],
                                                      font=("Consolas", 7, "bold"),
                                                      tags="link")

    def redraw(self):
        self._draw()


class PacketAnimation:
    """Animates a dot travelling along a link."""
    def __init__(self, canvas, x1, y1, x2, y2, color, callback=None):
        self.canvas   = canvas
        self.x1, self.y1 = x1, y1
        self.x2, self.y2 = x2, y2
        self.color    = color
        self.callback = callback
        self.steps    = 30
        self.step     = 0
        self.dot      = canvas.create_oval(x1-6, y1-6, x1+6, y1+6,
                                            fill=color, outline="white", width=1,
                                            tags="packet")
        self._tick()

    def _tick(self):
        if self.step >= self.steps:
            self.canvas.delete(self.dot)
            if self.callback: self.callback()
            return
        t  = self.step / self.steps
        cx = self.x1 + (self.x2 - self.x1) * t
        cy = self.y1 + (self.y2 - self.y1) * t
        self.canvas.coords(self.dot, cx-6, cy-6, cx+6, cy+6)
        self.step += 1
        self.canvas.after(25, self._tick)


class CLIWindow(tk.Toplevel):
    """Per-switch Cisco IOS-like CLI terminal."""

    def __init__(self, master, switch, app):
        super().__init__(master)
        self.switch = switch
        self.app    = app
        self.history     = []
        self.hist_idx    = -1

        self.title(f"CLI — {switch.hostname}")
        self.configure(bg=COLORS["cli_bg"])
        self.geometry("820x560")
        self.resizable(True, True)

        self._build_ui()
        self._print_banner()
        self._update_prompt()

        self.protocol("WM_DELETE_WINDOW", self.withdraw)

    def _build_ui(self):
        # Title bar
        hdr = tk.Frame(self, bg=COLORS["toolbar"], height=32)
        hdr.pack(fill="x")
        hdr.pack_propagate(False)
        tk.Label(hdr, text=f"  ⚡ Cisco IOS CLI  —  {self.switch.hostname}",
                 bg=COLORS["toolbar"], fg=COLORS["text"],
                 font=("Consolas", 10, "bold")).pack(side="left", pady=4)

        # Output area
        frame = tk.Frame(self, bg=COLORS["cli_bg"])
        frame.pack(fill="both", expand=True, padx=4, pady=4)

        self.output = scrolledtext.ScrolledText(
            frame, bg=COLORS["cli_bg"], fg=COLORS["cli_text"],
            font=("Consolas", 10), insertbackground=COLORS["cli_prompt"],
            selectbackground="#1e4e79", wrap="word",
            relief="flat", borderwidth=0, state="disabled",
        )
        self.output.pack(fill="both", expand=True)
        self.output.tag_config("prompt",  foreground=COLORS["cli_prompt"])
        self.output.tag_config("error",   foreground=COLORS["cli_error"])
        self.output.tag_config("info",    foreground=COLORS["cli_info"])
        self.output.tag_config("success", foreground=COLORS["green"])
        self.output.tag_config("warn",    foreground=COLORS["orange"])
        self.output.tag_config("cmd",     foreground="#ffffff")
        self.output.tag_config("dim",     foreground=COLORS["text_dim"])

        # Input row
        inp_frame = tk.Frame(self, bg=COLORS["cli_bg"])
        inp_frame.pack(fill="x", padx=4, pady=(0,4))

        self.prompt_var = tk.StringVar(value="Switch> ")
        self.prompt_lbl = tk.Label(inp_frame, textvariable=self.prompt_var,
                                   bg=COLORS["cli_bg"], fg=COLORS["cli_prompt"],
                                   font=("Consolas", 10, "bold"))
        self.prompt_lbl.pack(side="left")

        self.input_var = tk.StringVar()
        self.entry = tk.Entry(inp_frame, textvariable=self.input_var,
                              bg="#111111", fg=COLORS["cli_text"],
                              font=("Consolas", 10), insertbackground=COLORS["cli_prompt"],
                              relief="flat", borderwidth=0)
        self.entry.pack(side="left", fill="x", expand=True)
        self.entry.focus_set()
        self.entry.bind("<Return>",   self._on_enter)
        self.entry.bind("<Up>",       self._hist_up)
        self.entry.bind("<Down>",     self._hist_down)
        self.entry.bind("<Tab>",      self._on_tab)

    def _print_banner(self):
        banner = (
            "╔══════════════════════════════════════════════════════╗\n"
            "║    Layer 2 Switch Simulator  –  Cisco IOS CLI        ║\n"
            "║    Type '?' or 'help' for commands                   ║\n"
            "╚══════════════════════════════════════════════════════╝\n"
        )
        self._write(banner, "info")

    def _update_prompt(self):
        self.prompt_var.set(self.switch._prompt())

    def _write(self, text, tag=""):
        self.output.configure(state="normal")
        if text:
            self.output.insert("end", text + "\n", tag)
        self.output.configure(state="disabled")
        self.output.see("end")

    def _on_enter(self, event=None):
        cmd = self.input_var.get().strip()
        self.input_var.set("")
        if cmd:
            self.history.insert(0, cmd)
            if len(self.history) > 100: self.history.pop()
        self.hist_idx = -1

        # Echo command
        self._write(f"{self.switch._prompt()}{cmd}", "cmd")

        if not cmd:
            self._update_prompt()
            return

        result = self.switch.execute(cmd)
        if result == "__EXIT__":
            self._write("Closing CLI window...", "dim")
            self.after(500, self.withdraw)
        elif result:
            # Colour-code output
            tag = "info"
            if result.startswith("%"): tag = "error"
            elif "Error" in result or "DROPPED" in result: tag = "error"
            elif "Connected" in result or "[OK]" in result: tag = "success"
            elif "Warning" in result or "BPDU" in result: tag = "warn"
            self._write(result, tag)

        self._update_prompt()
        # Refresh canvas STP/links after each command
        self.app.redraw_all()

    def _hist_up(self, event=None):
        if not self.history: return
        self.hist_idx = min(self.hist_idx + 1, len(self.history) - 1)
        self.input_var.set(self.history[self.hist_idx])
        self.entry.icursor("end")

    def _hist_down(self, event=None):
        if self.hist_idx <= 0:
            self.hist_idx = -1; self.input_var.set(""); return
        self.hist_idx -= 1
        self.input_var.set(self.history[self.hist_idx])
        self.entry.icursor("end")

    def _on_tab(self, event=None):
        # Basic tab completion
        cmd = self.input_var.get().strip()
        completions = ["enable","disable","configure terminal","show","show interfaces",
                       "show interfaces status","show vlan brief","show mac-address-table",
                       "show spanning-tree","show running-config","show cdp neighbors",
                       "show log","show version","clear mac-address-table","clear counters",
                       "ping","write","reload","exit","end","?","hostname","interface",
                       "vlan","switchport mode access","switchport mode trunk",
                       "switchport access vlan","spanning-tree","no shutdown","shutdown"]
        for c in completions:
            if c.startswith(cmd) and c != cmd:
                self.input_var.set(c)
                self.entry.icursor("end")
                break
        return "break"

    def refresh_title(self):
        self.title(f"CLI — {self.switch.hostname}")
        self.prompt_var.set(self.switch._prompt())


class ConnectDialog(tk.Toplevel):
    """Dialog for connecting two switches via interface selection."""

    def __init__(self, master, switches, callback):
        super().__init__(master)
        self.switches = switches
        self.callback = callback
        self.title("Connect Switches")
        self.configure(bg=COLORS["panel"])
        self.geometry("420x300")
        self.resizable(False, False)
        self.grab_set()
        self._build()

    def _build(self):
        pad = {"padx": 10, "pady": 5}
        tk.Label(self, text="Connect Two Switches", bg=COLORS["panel"],
                 fg=COLORS["text"], font=("Consolas", 13, "bold")).pack(pady=10)

        names = list(self.switches.keys())

        for i, (lbl, row_var_sw, row_var_if) in enumerate([
            ("Switch 1:", "sw1_var", "if1_var"),
            ("Switch 2:", "sw2_var", "if2_var"),
        ]):
            frame = tk.Frame(self, bg=COLORS["panel"])
            frame.pack(fill="x", **pad)
            tk.Label(frame, text=lbl, bg=COLORS["panel"], fg=COLORS["text"],
                     font=("Consolas", 10), width=10, anchor="w").pack(side="left")

            sw_var = tk.StringVar(value=names[min(i, len(names)-1)])
            setattr(self, row_var_sw, sw_var)
            sw_cb  = ttk.Combobox(frame, textvariable=sw_var, values=names,
                                   width=14, state="readonly")
            sw_cb.pack(side="left", padx=4)

            if_var = tk.StringVar(value="GigabitEthernet0/1")
            setattr(self, row_var_if, if_var)
            if_cb  = ttk.Combobox(frame, textvariable=if_var, width=22, state="readonly")
            if_cb.pack(side="left", padx=4)
            setattr(self, f"if_cb_{i+1}", if_cb)

            def update_ifaces(event, sw_v=sw_var, if_v=if_var, cb=if_cb):
                sw = self.switches.get(sw_v.get())
                if sw:
                    free = [n for n, iface in sw.interfaces.items()
                            if iface.connected_to is None]
                    cb["values"] = free
                    if free: if_v.set(free[0])
            sw_cb.bind("<<ComboboxSelected>>", update_ifaces)
            update_ifaces(None)

        self.result_lbl = tk.Label(self, text="", bg=COLORS["panel"],
                                   fg=COLORS["red"], font=("Consolas", 9))
        self.result_lbl.pack()

        btn_frame = tk.Frame(self, bg=COLORS["panel"])
        btn_frame.pack(pady=15)
        tk.Button(btn_frame, text="Connect", bg=COLORS["blue"], fg="white",
                  font=("Consolas", 10, "bold"), relief="flat", padx=20,
                  command=self._connect).pack(side="left", padx=8)
        tk.Button(btn_frame, text="Cancel", bg=COLORS["toolbar"], fg="white",
                  font=("Consolas", 10), relief="flat", padx=20,
                  command=self.destroy).pack(side="left")

    def _connect(self):
        sw1  = self.switches.get(self.sw1_var.get())
        sw2  = self.switches.get(self.sw2_var.get())
        if1  = self.if1_var.get()
        if2  = self.if2_var.get()
        if sw1 is sw2:
            self.result_lbl.config(text="Cannot connect switch to itself!"); return
        msg = sw1.connect(if1, sw2, if2)
        if msg.startswith("%"):
            self.result_lbl.config(text=msg); return
        self.callback()
        self.destroy()


class SendFrameDialog(tk.Toplevel):
    """Dialog for simulating frame transmission with animation."""

    def __init__(self, master, switches, app):
        super().__init__(master)
        self.switches = switches
        self.app      = app
        self.title("Send Frame (Packet Simulation)")
        self.configure(bg=COLORS["panel"])
        self.geometry("460x340")
        self.resizable(False, False)
        self.grab_set()
        self._build()

    def _build(self):
        tk.Label(self, text="Simulate Frame Transmission", bg=COLORS["panel"],
                 fg=COLORS["text"], font=("Consolas", 13, "bold")).pack(pady=10)

        fields = [
            ("Switch:",   "sw_var",      list(self.switches.keys()), None),
            ("In Port:",  "port_var",    [], None),
            ("Src MAC:",  "src_mac_var", None, "AA:BB:CC:00:00:01"),
            ("Dst MAC:",  "dst_mac_var", None, "FF:FF:FF:FF:FF:FF"),
            ("VLAN:",     "vlan_var",    None, "1"),
        ]
        self.widgets = {}
        for lbl, var_name, choices, default in fields:
            frame = tk.Frame(self, bg=COLORS["panel"])
            frame.pack(fill="x", padx=16, pady=4)
            tk.Label(frame, text=lbl, bg=COLORS["panel"], fg=COLORS["text"],
                     font=("Consolas", 10), width=10, anchor="w").pack(side="left")
            if choices is not None:
                var = tk.StringVar(value=(choices[0] if choices else ""))
                setattr(self, var_name, var)
                cb  = ttk.Combobox(frame, textvariable=var, values=choices,
                                   width=28, state="readonly")
                cb.pack(side="left")
                self.widgets[var_name] = cb
            else:
                var = tk.StringVar(value=default or "")
                setattr(self, var_name, var)
                ent = tk.Entry(frame, textvariable=var, bg="#111",
                               fg=COLORS["cli_text"], font=("Consolas", 10),
                               insertbackground="white", width=30)
                ent.pack(side="left")

        # Update port list when switch changes
        def on_sw_change(event=None):
            sw = self.switches.get(self.sw_var.get())
            if sw:
                ports = list(sw.interfaces.keys())
                self.widgets["port_var"]["values"] = ports
                self.port_var.set(ports[0] if ports else "")
        if "sw_var" in self.widgets:
            self.widgets["sw_var"].bind("<<ComboboxSelected>>", on_sw_change)
            on_sw_change()

        self.result = scrolledtext.ScrolledText(self, bg=COLORS["cli_bg"],
                                                 fg=COLORS["cli_text"],
                                                 font=("Consolas", 9),
                                                 height=5, state="disabled",
                                                 relief="flat")
        self.result.pack(fill="x", padx=16, pady=8)

        btn_frame = tk.Frame(self, bg=COLORS["panel"])
        btn_frame.pack(pady=8)
        tk.Button(btn_frame, text="Send Frame", bg=COLORS["green"], fg="black",
                  font=("Consolas", 10, "bold"), relief="flat", padx=20,
                  command=self._send).pack(side="left", padx=8)
        tk.Button(btn_frame, text="Close", bg=COLORS["toolbar"], fg="white",
                  font=("Consolas", 10), relief="flat", padx=20,
                  command=self.destroy).pack(side="left")

    def _send(self):
        sw   = self.switches.get(self.sw_var.get())
        port = self.port_var.get()
        src  = self.src_mac_var.get()
        dst  = self.dst_mac_var.get()
        try:
            vlan = int(self.vlan_var.get())
        except ValueError:
            vlan = 1

        if not sw: return
        result = sw.send_frame(src, dst, vlan, port)

        self.result.configure(state="normal")
        self.result.delete("1.0", "end")
        self.result.insert("end", result)
        self.result.configure(state="disabled")

        # Animate on canvas
        self.app.animate_frame(sw.hostname, port, dst)
        self.app.redraw_all()


class App(tk.Tk):
    """Main application window — Packet Tracer-like UI."""

    def __init__(self):
        super().__init__()
        self.title("Switch Simulator — Packet Tracer Edition")
        self.geometry("1400x860")
        self.configure(bg=COLORS["bg"])
        self.minsize(900, 600)

        self.switches   = {}   # hostname -> Switch
        self.nodes      = {}   # hostname -> SwitchNode
        self.links      = []   # list of LinkLine
        self.cli_wins   = {}   # hostname -> CLIWindow
        self.selected   = None
        self._drag_start = None

        self._build_menu()
        self._build_toolbar()
        self._build_main()
        self._build_statusbar()

        self._canvas_mode = "select"   # "select" | "addswitch" | "connect"
        self._connect_step = 0
        self._connect_node1 = None

        self._refresh_loop()

    # ── Layout ────────────────────────────────────────

    def _build_menu(self):
        mb = tk.Menu(self, bg=COLORS["panel"], fg=COLORS["text"],
                     activebackground=COLORS["toolbar"])
        self.config(menu=mb)

        file_m = tk.Menu(mb, tearoff=0, bg=COLORS["panel"], fg=COLORS["text"])
        mb.add_cascade(label="File", menu=file_m)
        file_m.add_command(label="New Topology",     command=self._new_topology)
        file_m.add_command(label="Open Topology…",   command=self._open_topology)
        file_m.add_command(label="Save Topology…",   command=self._save_topology)
        file_m.add_separator()
        file_m.add_command(label="Exit",             command=self.quit)

        topo_m = tk.Menu(mb, tearoff=0, bg=COLORS["panel"], fg=COLORS["text"])
        mb.add_cascade(label="Topology", menu=topo_m)
        topo_m.add_command(label="Add Switch",       command=self._add_switch_click)
        topo_m.add_command(label="Connect Switches…",command=self._open_connect_dialog)
        topo_m.add_command(label="Load Demo Topology",command=self._load_demo)
        topo_m.add_separator()
        topo_m.add_command(label="Delete Selected",  command=self._delete_selected)

        sim_m = tk.Menu(mb, tearoff=0, bg=COLORS["panel"], fg=COLORS["text"])
        mb.add_cascade(label="Simulate", menu=sim_m)
        sim_m.add_command(label="Send Frame…",       command=self._open_send_frame)
        sim_m.add_command(label="Recalculate STP",   command=self._recalc_stp)

        help_m = tk.Menu(mb, tearoff=0, bg=COLORS["panel"], fg=COLORS["text"])
        mb.add_cascade(label="Help", menu=help_m)
        help_m.add_command(label="About",            command=self._about)

    def _build_toolbar(self):
        tb = tk.Frame(self, bg=COLORS["toolbar"], height=48)
        tb.pack(fill="x")
        tb.pack_propagate(False)

        self._tool_buttons = {}

        def tool_btn(text, cmd, color=None, tip=""):
            c = color or COLORS["toolbar"]
            b = tk.Button(tb, text=text, bg=c, fg="white",
                          font=("Segoe UI", 9, "bold"), relief="flat",
                          padx=10, pady=4, command=cmd,
                          activebackground=COLORS["blue"], cursor="hand2")
            b.pack(side="left", padx=2, pady=8)
            return b

        self._tool_buttons["select"]  = tool_btn("↖  Select",      self._mode_select)
        self._tool_buttons["switch"]  = tool_btn("🖧  Add Switch",   self._mode_addswitch, COLORS["blue"])
        self._tool_buttons["connect"] = tool_btn("⚡  Connect",      self._mode_connect,  COLORS["cyan"])
        tool_btn("🗑  Delete",       self._delete_selected, COLORS["red"])
        tool_btn("⚙  Send Frame",   self._open_send_frame, COLORS["toolbar"])
        tool_btn("♻  STP Recalc",   self._recalc_stp)
        tool_btn("💾  Save",         self._save_topology)
        tool_btn("📂  Open",         self._open_topology)
        tool_btn("🔄  Demo",         self._load_demo)

        # Mode indicator
        self.mode_lbl = tk.Label(tb, text="Mode: Select",
                                  bg=COLORS["toolbar"], fg=COLORS["yellow"],
                                  font=("Consolas", 10, "bold"))
        self.mode_lbl.pack(side="right", padx=14)

    def _build_main(self):
        paned = tk.PanedWindow(self, orient="horizontal",
                               bg=COLORS["bg"], sashwidth=5, sashrelief="raised")
        paned.pack(fill="both", expand=True)

        # Left: canvas
        canvas_frame = tk.Frame(paned, bg=COLORS["canvas_bg"])
        self.canvas  = tk.Canvas(canvas_frame, bg=COLORS["canvas_bg"],
                                  highlightthickness=0, cursor="crosshair")
        self.canvas.pack(fill="both", expand=True)
        paned.add(canvas_frame, minsize=600)

        # Grid lines
        self._draw_grid()

        self.canvas.bind("<Button-1>",        self._canvas_click)
        self.canvas.bind("<B1-Motion>",       self._canvas_drag)
        self.canvas.bind("<ButtonRelease-1>", self._canvas_release)
        self.canvas.bind("<Double-Button-1>", self._canvas_dblclick)
        self.canvas.bind("<Button-3>",        self._canvas_right_click)
        self.canvas.bind("<Configure>",       lambda e: self._draw_grid())

        # Right: info panel
        right  = tk.Frame(paned, bg=COLORS["panel"], width=300)
        paned.add(right, minsize=220)

        tk.Label(right, text="  Switch Info", bg=COLORS["panel"],
                 fg=COLORS["text"], font=("Consolas", 11, "bold"),
                 anchor="w").pack(fill="x", pady=(8,2))
        ttk.Separator(right).pack(fill="x")

        self.info_text = scrolledtext.ScrolledText(
            right, bg=COLORS["panel"], fg=COLORS["text"],
            font=("Consolas", 9), relief="flat", state="disabled",
            wrap="word")
        self.info_text.pack(fill="both", expand=True, padx=4, pady=4)

        tk.Label(right, text="  Switches", bg=COLORS["panel"],
                 fg=COLORS["text"], font=("Consolas", 11, "bold"),
                 anchor="w").pack(fill="x")
        ttk.Separator(right).pack(fill="x")

        self.sw_list_frame = tk.Frame(right, bg=COLORS["panel"])
        self.sw_list_frame.pack(fill="x", padx=4, pady=4)

    def _build_statusbar(self):
        sb = tk.Frame(self, bg=COLORS["toolbar"], height=24)
        sb.pack(fill="x", side="bottom")
        sb.pack_propagate(False)
        self.status_var = tk.StringVar(value="Ready — right-click canvas for menu")
        tk.Label(sb, textvariable=self.status_var, bg=COLORS["toolbar"],
                 fg=COLORS["text"], font=("Consolas", 9)).pack(side="left", padx=8)
        self.clock_var = tk.StringVar()
        tk.Label(sb, textvariable=self.clock_var, bg=COLORS["toolbar"],
                 fg=COLORS["text_dim"], font=("Consolas", 9)).pack(side="right", padx=8)

    def _draw_grid(self):
        self.canvas.delete("grid")
        w = self.canvas.winfo_width() or 1400
        h = self.canvas.winfo_height() or 800
        step = 40
        for x in range(0, w, step):
            self.canvas.create_line(x, 0, x, h, fill="#1e1e30", tags="grid")
        for y in range(0, h, step):
            self.canvas.create_line(0, y, w, y, fill="#1e1e30", tags="grid")
        self.canvas.tag_lower("grid")

    # ── Toolbar modes ──────────────────────────────────

    def _mode_select(self):
        self._canvas_mode = "select"
        self.mode_lbl.config(text="Mode: Select")
        self.canvas.config(cursor="arrow")
        self._update_tool_highlights()

    def _mode_addswitch(self):
        self._canvas_mode = "addswitch"
        self.mode_lbl.config(text="Mode: Add Switch  (click canvas)")
        self.canvas.config(cursor="crosshair")
        self._update_tool_highlights()

    def _mode_connect(self):
        self._canvas_mode = "connect"
        self._connect_step = 0
        self.mode_lbl.config(text="Mode: Connect  (click switch 1)")
        self.canvas.config(cursor="tcross")
        self._update_tool_highlights()

    def _update_tool_highlights(self):
        for key, btn in self._tool_buttons.items():
            if key == self._canvas_mode:
                btn.config(relief="sunken", bg=COLORS["yellow"], fg="black")
            else:
                default_colors = {"select": COLORS["toolbar"], "switch": COLORS["blue"],
                                  "connect": COLORS["cyan"]}
                btn.config(relief="flat", bg=default_colors.get(key, COLORS["toolbar"]), fg="white")

    # ── Canvas events ──────────────────────────────────

    def _canvas_click(self, event):
        ex, ey = event.x, event.y
        node   = self._hit_node(ex, ey)

        if self._canvas_mode == "addswitch":
            self._add_switch_at(ex, ey)
            return

        if self._canvas_mode == "connect":
            if node:
                if self._connect_step == 0:
                    self._connect_node1 = node
                    self._connect_step  = 1
                    self.mode_lbl.config(text=f"Mode: Connect  ({node.switch.hostname} selected — click switch 2)")
                    self._set_status(f"Click second switch to connect to {node.switch.hostname}")
                else:
                    if node is not self._connect_node1:
                        self._open_connect_dialog(node1=self._connect_node1, node2=node)
                    self._connect_step  = 0
                    self._connect_node1 = None
                    self.mode_lbl.config(text="Mode: Connect  (click switch 1)")
            return

        # Select mode
        if node:
            self._select(node)
            self._drag_start = (ex, ey)
        else:
            self._deselect()

    def _canvas_drag(self, event):
        if self._canvas_mode != "select": return
        if not self.selected or not self._drag_start: return
        dx = event.x - self._drag_start[0]
        dy = event.y - self._drag_start[1]
        self.selected.move(dx, dy)
        self._drag_start = (event.x, event.y)
        self._redraw_links()

    def _canvas_release(self, event):
        self._drag_start = None

    def _canvas_dblclick(self, event):
        node = self._hit_node(event.x, event.y)
        if node:
            self._open_cli(node.switch)

    def _canvas_right_click(self, event):
        node = self._hit_node(event.x, event.y)
        menu = tk.Menu(self, tearoff=0, bg=COLORS["panel"], fg=COLORS["text"])
        if node:
            menu.add_command(label=f"Open CLI — {node.switch.hostname}",
                             command=lambda: self._open_cli(node.switch))
            menu.add_command(label="Connect to…",
                             command=lambda: self._open_connect_dialog(node1=node))
            menu.add_command(label="Delete Switch",
                             command=lambda: self._delete_node(node))
            menu.add_separator()
            menu.add_command(label="Properties",
                             command=lambda: self._show_properties(node))
        else:
            menu.add_command(label="Add Switch Here",
                             command=lambda: self._add_switch_at(event.x, event.y))
            menu.add_command(label="Connect Switches…",
                             command=self._open_connect_dialog)
            menu.add_command(label="Load Demo",
                             command=self._load_demo)
        menu.tk_popup(event.x_root, event.y_root)

    # ── Switch management ──────────────────────────────

    def _add_switch_click(self):
        self._mode_addswitch()

    def _add_switch_at(self, x, y):
        n = len(self.switches) + 1
        # Find a unique hostname
        base = f"SW{n}"
        while base in self.switches:
            n += 1; base = f"SW{n}"

        # Ask for name
        name = self._ask_name("New Switch", f"Hostname:", base)
        if not name: return
        if name in self.switches:
            messagebox.showerror("Error", f"Switch '{name}' already exists.")
            return

        sw   = Switch(name)
        node = SwitchNode(self.canvas, sw, x, y)
        self.switches[name] = sw
        self.nodes[name]    = node
        self._refresh_sw_list()
        self._set_status(f"Added switch '{name}'")
        self._mode_select()

    def _ask_name(self, title, prompt, default=""):
        dlg = tk.Toplevel(self)
        dlg.title(title)
        dlg.configure(bg=COLORS["panel"])
        dlg.geometry("320x130")
        dlg.resizable(False, False)
        dlg.grab_set()
        tk.Label(dlg, text=prompt, bg=COLORS["panel"], fg=COLORS["text"],
                 font=("Consolas", 10)).pack(pady=10)
        var = tk.StringVar(value=default)
        ent = tk.Entry(dlg, textvariable=var, font=("Consolas", 12),
                       bg="#111", fg=COLORS["cli_text"], insertbackground="white")
        ent.pack(padx=20, fill="x")
        ent.select_range(0, "end"); ent.focus_set()
        result = [None]
        def ok(e=None): result[0] = var.get().strip(); dlg.destroy()
        def cancel():   dlg.destroy()
        bf = tk.Frame(dlg, bg=COLORS["panel"]); bf.pack(pady=8)
        tk.Button(bf, text="OK", command=ok, bg=COLORS["blue"], fg="white",
                  relief="flat", padx=14).pack(side="left", padx=6)
        tk.Button(bf, text="Cancel", command=cancel, bg=COLORS["toolbar"],
                  fg="white", relief="flat", padx=14).pack(side="left")
        ent.bind("<Return>", ok)
        dlg.wait_window()
        return result[0]

    def _delete_selected(self):
        if self.selected:
            self._delete_node(self.selected)

    def _delete_node(self, node):
        sw = node.switch
        if not messagebox.askyesno("Delete Switch",
                                   f"Delete '{sw.hostname}' and all its links?"):
            return
        # Remove links
        remove = [lk for lk in self.links
                  if lk.node1 is node or lk.node2 is node]
        for lk in remove:
            sw.disconnect_iface(lk.if1)
            for item in [lk.line, lk.label1, lk.label2, lk.stp_badge]:
                if item: self.canvas.delete(item)
            self.links.remove(lk)
        # Remove node
        for item in node.items:
            self.canvas.delete(item)
        del self.switches[sw.hostname]
        del self.nodes[sw.hostname]
        if sw.hostname in self.cli_wins:
            self.cli_wins[sw.hostname].destroy()
            del self.cli_wins[sw.hostname]
        if self.selected is node:
            self.selected = None
        self._refresh_sw_list()
        self._set_status(f"Deleted switch '{sw.hostname}'")

    # ── Connect dialog ─────────────────────────────────

    def _open_connect_dialog(self, node1=None, node2=None):
        if len(self.switches) < 2:
            messagebox.showinfo("Connect", "Need at least 2 switches to connect.")
            return
        dlg = ConnectDialog(self, self.switches, self._on_connected)
        if node1:
            if hasattr(dlg, "sw1_var"):
                dlg.sw1_var.set(node1.switch.hostname)
        if node2:
            if hasattr(dlg, "sw2_var"):
                dlg.sw2_var.set(node2.switch.hostname)

    def _on_connected(self):
        self._rebuild_links()
        self.redraw_all()
        self._set_status("Switches connected.")

    def _rebuild_links(self):
        """Rebuild link visuals from switch topology."""
        # Clear old
        for lk in self.links:
            for item in [lk.line, lk.label1, lk.label2, lk.stp_badge]:
                if item: self.canvas.delete(item)
        self.links.clear()

        seen = set()
        for sw in self.switches.values():
            node1 = self.nodes.get(sw.hostname)
            if not node1: continue
            for iface in sw.interfaces.values():
                if not iface.connected_to: continue
                peer_name, peer_if = iface.connected_to
                key = tuple(sorted([(sw.hostname, iface.name), (peer_name, peer_if)]))
                if key in seen: continue
                seen.add(key)
                node2 = self.nodes.get(peer_name)
                if not node2: continue
                lk = LinkLine(self.canvas, node1, iface.name, node2, peer_if)
                self.links.append(lk)
                self.canvas.tag_lower("link")
                self.canvas.tag_lower("grid")

    def _redraw_links(self):
        for lk in self.links:
            lk.redraw()
        self.canvas.tag_lower("link")
        self.canvas.tag_lower("grid")

    # ── STP & refresh ──────────────────────────────────

    def _recalc_stp(self):
        for sw in self.switches.values():
            sw.stp.recalculate()
        self.redraw_all()
        self._set_status("STP recalculated.")

    def redraw_all(self):
        for node in self.nodes.values():
            node.redraw()
        self._redraw_links()
        self._update_info_panel()
        self._refresh_sw_list()
        for win in self.cli_wins.values():
            win.refresh_title()

    def _refresh_loop(self):
        self.clock_var.set(datetime.now().strftime("%H:%M:%S"))
        self._redraw_links()
        for node in self.nodes.values():
            node.redraw()
        self.after(2000, self._refresh_loop)

    # ── Packet animation ───────────────────────────────

    def animate_frame(self, sw_hostname, in_port, dst_mac):
        """Visualise a frame leaving the switch on matching links."""
        sw   = self.switches.get(sw_hostname)
        node = self.nodes.get(sw_hostname)
        if not sw or not node: return

        colors = {"flood": COLORS["yellow"], "forward": COLORS["green"]}

        # Find links from this switch
        for lk in self.links:
            if lk.node1.switch.hostname == sw_hostname:
                out_node = lk.node2; x1,y1=lk.node1.x,lk.node1.y; x2,y2=lk.node2.x,lk.node2.y
            elif lk.node2.switch.hostname == sw_hostname:
                out_node = lk.node1; x1,y1=lk.node2.x,lk.node2.y; x2,y2=lk.node1.x,lk.node1.y
            else:
                continue
            color = COLORS["yellow"]
            PacketAnimation(self.canvas, x1, y1, x2, y2, color)

    # ── Info panel ─────────────────────────────────────

    def _select(self, node):
        if self.selected:
            self.selected.selected = False
            self.selected.redraw()
        self.selected = node
        node.selected = True
        node.redraw()
        self._update_info_panel()

    def _deselect(self):
        if self.selected:
            self.selected.selected = False
            self.selected.redraw()
        self.selected = None
        self._update_info_panel()

    def _update_info_panel(self):
        self.info_text.configure(state="normal")
        self.info_text.delete("1.0", "end")
        if self.selected:
            sw = self.selected.switch
            text = (
                f"Hostname   : {sw.hostname}\n"
                f"STP Root   : {'YES ♛' if sw.stp.is_root() else 'no'}\n"
                f"STP Priority: {sw.stp.bridge_priority}\n"
                f"Bridge ID  : {sw.stp.bridge_id}\n"
                f"VLANs      : {', '.join(str(v) for v in sorted(sw.vlans.keys()))}\n"
                f"Interfaces : {len(sw.interfaces)}\n"
                f"MAC Entries: {len(sw.mac_table)}\n"
                f"\nConnections:\n"
            )
            for iface in sw.interfaces.values():
                if iface.connected_to:
                    short = iface.name.replace("FastEthernet0/","Fa0/").replace("GigabitEthernet0/","Gi0/")
                    peer_sw, peer_if = iface.connected_to
                    peer_short = peer_if.replace("FastEthernet0/","Fa0/").replace("GigabitEthernet0/","Gi0/")
                    stp = iface.stp_state.value
                    text += f"  {short} → {peer_sw}/{peer_short}  [{stp}]\n"
            self.info_text.insert("end", text)
        else:
            self.info_text.insert("end",
                "No switch selected.\n\nClick a switch to see its info.\nDouble-click to open CLI.")
        self.info_text.configure(state="disabled")

    def _refresh_sw_list(self):
        for w in self.sw_list_frame.winfo_children():
            w.destroy()
        for name, sw in self.switches.items():
            node = self.nodes.get(name)
            row  = tk.Frame(self.sw_list_frame, bg=COLORS["panel"])
            row.pack(fill="x", pady=1)
            root_mark = " ♛" if sw.stp.is_root() else ""
            color = COLORS["yellow"] if sw.stp.is_root() else COLORS["text"]
            tk.Label(row, text=f"  {name}{root_mark}", bg=COLORS["panel"],
                     fg=color, font=("Consolas", 9)).pack(side="left", fill="x", expand=True)
            tk.Button(row, text="CLI", bg=COLORS["blue"], fg="white",
                      font=("Consolas", 8), relief="flat", padx=4,
                      command=lambda s=sw: self._open_cli(s)).pack(side="right", padx=2)

    # ── CLI ────────────────────────────────────────────

    def _open_cli(self, switch):
        name = switch.hostname
        if name in self.cli_wins and self.cli_wins[name].winfo_exists():
            win = self.cli_wins[name]
            win.deiconify()
            win.lift()
            win.focus_force()
        else:
            win = CLIWindow(self, switch, self)
            self.cli_wins[name] = win

    # ── Context menu helpers ───────────────────────────

    def _show_properties(self, node):
        sw   = node.switch
        info = (
            f"Switch: {sw.hostname}\n"
            f"STP Priority: {sw.stp.bridge_priority}\n"
            f"Bridge ID: {sw.stp.bridge_id}\n"
            f"Is Root: {sw.stp.is_root()}\n"
            f"Interfaces: {len(sw.interfaces)}\n"
            f"MAC entries: {len(sw.mac_table)}\n"
            f"VLANs: {list(sw.vlans.keys())}\n"
        )
        messagebox.showinfo(f"Properties — {sw.hostname}", info)

    # ── Hit test ───────────────────────────────────────

    def _hit_node(self, x, y):
        for node in self.nodes.values():
            if node.hit_test(x, y):
                return node
        return None

    # ── Save / Load ────────────────────────────────────

    def _save_topology(self):
        path = filedialog.asksaveasfilename(
            defaultextension=".json",
            filetypes=[("JSON Topology", "*.json"), ("All Files", "*.*")],
            title="Save Topology",
        )
        if not path: return
        data = {
            "switches": {name: sw.to_dict() for name, sw in self.switches.items()},
            "positions": {name: [node.x, node.y] for name, node in self.nodes.items()},
        }
        with open(path, "w") as f:
            json.dump(data, f, indent=2)
        self._set_status(f"Saved to {path}")

    def _open_topology(self):
        path = filedialog.askopenfilename(
            filetypes=[("JSON Topology", "*.json"), ("All Files", "*.*")],
            title="Open Topology",
        )
        if not path: return
        try:
            with open(path) as f:
                data = json.load(f)
            self._new_topology(confirm=False)
            positions = data.get("positions", {})
            for name, sw_dict in data["switches"].items():
                sw   = Switch.from_dict(sw_dict)
                pos  = positions.get(name, [200 + len(self.switches)*120, 300])
                node = SwitchNode(self.canvas, sw, pos[0], pos[1])
                self.switches[name] = sw
                self.nodes[name]    = node
            # Restore topology references
            for name, sw in self.switches.items():
                for iface in sw.interfaces.values():
                    if iface.connected_to:
                        peer_name = iface.connected_to[0]
                        if peer_name in self.switches:
                            sw.topology[peer_name] = self.switches[peer_name]
            for sw in self.switches.values():
                sw.stp.recalculate()
            self._rebuild_links()
            self._refresh_sw_list()
            self._set_status(f"Loaded {path}")
        except Exception as e:
            messagebox.showerror("Load Error", str(e))

    def _new_topology(self, confirm=True):
        if confirm and self.switches:
            if not messagebox.askyesno("New Topology", "Clear current topology?"):
                return
        for win in self.cli_wins.values():
            try: win.destroy()
            except: pass
        self.cli_wins.clear()
        self.canvas.delete("all")
        self.switches.clear()
        self.nodes.clear()
        self.links.clear()
        self.selected = None
        self._draw_grid()
        self._refresh_sw_list()
        self._update_info_panel()
        self._set_status("New topology created.")

    # ── Demo ───────────────────────────────────────────

    def _load_demo(self):
        self._new_topology(confirm=len(self.switches) > 0)

        cx, cy  = self.canvas.winfo_width()//2 or 600, self.canvas.winfo_height()//2 or 400
        w, h    = 220, 160

        positions = {
            "CoreSW":    (cx, cy - h),
            "AccessSW1": (cx - w, cy + h//2),
            "AccessSW2": (cx + w, cy + h//2),
        }

        for name in ("CoreSW", "AccessSW1", "AccessSW2"):
            sw   = Switch(name)
            x, y = positions[name]
            node = SwitchNode(self.canvas, sw, x, y)
            self.switches[name] = sw
            self.nodes[name]    = node

        cs  = self.switches["CoreSW"]
        a1  = self.switches["AccessSW1"]
        a2  = self.switches["AccessSW2"]

        for vid, vname in [(10,"Sales"),(20,"Engineering"),(30,"Management")]:
            for sw in (cs, a1, a2):
                sw.vlans[vid] = VLAN(vid, vname)

        for sw in (cs, a1, a2):
            for gi in ("GigabitEthernet0/1", "GigabitEthernet0/2"):
                sw.interfaces[gi].mode = PortMode.TRUNK

        def set_access(sw, lo, hi, vid):
            for i in range(lo, hi+1):
                iface = sw._get_iface(f"FastEthernet0/{i}")
                if iface:
                    iface.mode        = PortMode.ACCESS
                    iface.access_vlan = vid

        for sw in (a1, a2):
            set_access(sw, 1, 8, 10); set_access(sw, 9, 16, 20); set_access(sw, 17, 24, 30)

        cs.stp.set_priority(4096)

        cs.connect("GigabitEthernet0/1", a1, "GigabitEthernet0/1")
        cs.connect("GigabitEthernet0/2", a2, "GigabitEthernet0/1")
        a1.connect("GigabitEthernet0/2", a2, "GigabitEthernet0/2")

        for sw in (cs, a1, a2):
            sw.stp.recalculate()

        for mac, sw, port, vlan in [
            ("AA:BB:CC:00:00:01", a1, "FastEthernet0/1",  10),
            ("AA:BB:CC:00:00:02", a1, "FastEthernet0/9",  20),
            ("AA:BB:CC:00:00:03", a2, "FastEthernet0/1",  10),
            ("AA:BB:CC:00:00:04", a2, "FastEthernet0/17", 30),
        ]:
            sw.mac_table[(mac, vlan)] = MACEntry(mac, port, vlan)

        self._rebuild_links()
        self._refresh_sw_list()
        self._set_status("Demo topology loaded (CoreSW + 2 Access switches, VLANs 10/20/30, STP)")

    # ── Send Frame ─────────────────────────────────────

    def _open_send_frame(self):
        if not self.switches:
            messagebox.showinfo("Send Frame", "Add switches first.")
            return
        SendFrameDialog(self, self.switches, self)

    # ── About ──────────────────────────────────────────

    def _about(self):
        messagebox.showinfo("About", (
            "Switch Simulator — Packet Tracer Edition\n\n"
            "Features:\n"
            "  • Drag-and-drop topology design\n"
            "  • Per-switch Cisco IOS CLI\n"
            "  • Interface-level connections (Fa0/x, Gi0/x)\n"
            "  • Link status (green/orange/red)\n"
            "  • STP visualization (blocked ports, root bridge)\n"
            "  • Packet simulation with animation\n"
            "  • VLAN, trunk, MAC table support\n"
            "  • Save/load topology (JSON)\n"
            "  • Tab completion & command history\n"
        ))

    # ── Misc helpers ───────────────────────────────────

    def _set_status(self, msg):
        self.status_var.set(msg)


# ─────────────────────────────────────────────────────
#  ENTRY POINT
# ─────────────────────────────────────────────────────

if __name__ == "__main__":
    app = App()
    app.mainloop()
