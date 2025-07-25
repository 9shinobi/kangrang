import base58
import hashlib
from collections import defaultdict
import re
import random
import time
from ecdsa import SigningKey, SECP256k1
import math
import multiprocessing
from concurrent.futures import ProcessPoolExecutor, ThreadPoolExecutor
import itertools
from functools import partial
import threading
import queue

def hash160(data: bytes) -> bytes:
    return hashlib.new('ripemd160', hashlib.sha256(data).digest()).digest()

def base58_from_h160(h160: bytes) -> str:
    versioned = b'\x00' + h160
    checksum = hashlib.sha256(hashlib.sha256(versioned).digest()).digest()[:4]
    return base58.b58encode(versioned + checksum).decode()

def private_key_to_compressed_public_key(private_key_hex):
    """Konvertiert Private Key zu komprimiertem Public Key mit ecdsa"""
    try:
        private_key_bytes = bytes.fromhex(private_key_hex)
        sk = SigningKey.from_string(private_key_bytes, curve=SECP256k1)
        vk = sk.get_verifying_key()
        compressed_pubkey = vk.to_string("compressed")
        return compressed_pubkey
    except Exception as e:
        raise ValueError(f"Fehler beim Verarbeiten des Private Keys: {str(e)}")

def get_target_hash160(target_address):
    try:
        decoded = base58.b58decode(target_address)
        if len(decoded) == 25:
            return decoded[1:21]
    except:
        pass
    return None

def hash160_to_int(h160_bytes):
    """Konvertiert Hash160 zu Integer für Berechnungen"""
    return int.from_bytes(h160_bytes, byteorder='big')

def int_to_hash160(value):
    """Konvertiert Integer zurück zu Hash160 (20 Bytes)"""
    return value.to_bytes(20, byteorder='big')

def get_jump_table():
    """Erstellt Jump-Tabelle basierend auf Hash160-Eigenschaften"""
    jump_table = {}
    
    # Basis-Jumps basierend auf den letzten 12 Bits des Hash160
    for i in range(4096):  # 2^12 = 4096
        # Verschiedene Jump-Größen basierend auf Mustern
        if i & 0x001 == 0:  # Letztes Bit 0
            jump_size = 2**18 + (i & 0x3FF) * 1000
        elif i & 0x003 == 1:  # Letzte 2 Bits: 01
            jump_size = 2**17 + (i & 0x1FF) * 2000
        elif i & 0x007 == 3:  # Letzte 3 Bits: 011
            jump_size = 2**16 + (i & 0xFF) * 3000
        elif i & 0x00F == 4:  # Letzte 4 Bits: 0111
            jump_size = 2**15 + (i & 0x7F) * 4000
        elif i & 0x01F == 15:  # Letzte 5 Bits: 01111
            jump_size = 2**14 + (i & 0x3F) * 5000
        else:
            jump_size = 2**13 + (i & 0x1FF) * 1500
        
        jump_table[i] = min(jump_size, 2**20)  # Max Jump: 1M
    
    return jump_table

def get_jump_size(hash160_int, jump_table):
    """Berechnet Jump-Größe basierend auf Hash160-Wert"""
    index = hash160_int & 0xFFF  # Letzte 12 Bits
    return jump_table[index]

class Hash160Kangaroo:
    def __init__(self, range_start, range_end, target_hash160, jump_table, kangaroo_id, kangaroo_type):
        self.range_start = range_start
        self.range_end = range_end
        self.target_hash160 = target_hash160
        self.target_hash160_int = hash160_to_int(target_hash160)
        self.jump_table = jump_table
        self.kangaroo_id = kangaroo_id
        self.kangaroo_type = kangaroo_type  # 'tame' oder 'wild'
        
        # Kangaroo-Position und Distanz
        if kangaroo_type == 'tame':
            # Zahmes Kangaroo startet am Anfang des Bereichs
            self.current_key = range_start
            self.distance = 0
        else:
            # Wildes Kangaroo startet zufällig im Bereich
            self.current_key = random.randint(range_start, range_end)
            self.distance = random.randint(0, (range_end - range_start) // 100)
        
        self.current_hash160_int = None
        self.path = []  # Speichert (key, hash160_int, distance) für Kollisionserkennung
        self.max_path_length = 5000  # Begrenze Pfad-Speicher
        
        # Berechne initiales Hash160
        self.update_current_hash160()
    
    def update_current_hash160(self):
        """Berechnet Hash160 für aktuellen Key"""
        try:
            hexkey = f"{self.current_key:064x}"
            compressed_pubkey = private_key_to_compressed_public_key(hexkey)
            h160 = hash160(compressed_pubkey)
            self.current_hash160_int = hash160_to_int(h160)
            
            # Speichere in Pfad für Kollisionserkennung
            if len(self.path) < self.max_path_length:
                self.path.append((self.current_key, self.current_hash160_int, self.distance))
            
            return h160
        except Exception as e:
            # Bei Fehler: Springe zu neuem zufälligen Key
            self.current_key = random.randint(self.range_start, self.range_end)
            return None
    
    def make_jump(self):
        """Führt einen Sprung des Kangaroos aus"""
        if self.current_hash160_int is None:
            self.update_current_hash160()
            return
        
        # Berechne Jump-Größe basierend auf aktuellem Hash160
        jump_size = get_jump_size(self.current_hash160_int, self.jump_table)
        
        # Führe Sprung aus
        if self.kangaroo_type == 'tame':
            # Zahmes Kangaroo springt vorwärts
            new_key = self.current_key + jump_size
        else:
            # Wildes Kangaroo kann in beide Richtungen springen
            direction = 1 if (self.current_hash160_int & 1) == 0 else -1
            new_key = self.current_key + (jump_size * direction)
        
        # Halte Kangaroo im Bereich
        if new_key < self.range_start:
            new_key = self.range_start + (self.range_start - new_key) % (self.range_end - self.range_start)
        elif new_key > self.range_end:
            new_key = self.range_start + (new_key - self.range_start) % (self.range_end - self.range_start)
        
        self.current_key = new_key
        self.distance += jump_size
        
        # Update Hash160
        self.update_current_hash160()
    
    def check_target_collision(self):
        """Prüft ob aktueller Hash160 dem Ziel entspricht"""
        if self.current_hash160_int is None:
            return None
        
        current_h160_bytes = int_to_hash160(self.current_hash160_int)
        
        # Exakte Übereinstimmung
        if current_h160_bytes == self.target_hash160:
            return {
                'type': 'exact_match',
                'key': f"{self.current_key:064x}",
                'hash160': current_h160_bytes.hex(),
                'address': base58_from_h160(current_h160_bytes),
                'distance': self.distance,
                'kangaroo_id': self.kangaroo_id,
                'kangaroo_type': self.kangaroo_type
            }
        
        # Präfix-Match (erste 4 Bytes)
        if current_h160_bytes[:4] == self.target_hash160[:4]:
            return {
                'type': 'prefix_match',
                'key': f"{self.current_key:064x}",
                'hash160': current_h160_bytes.hex(),
                'address': base58_from_h160(current_h160_bytes),
                'distance': self.distance,
                'kangaroo_id': self.kangaroo_id,
                'kangaroo_type': self.kangaroo_type,
                'match_bytes': 4
            }
        
        return None

class KangarooCollisionDetector:
    def __init__(self, max_entries=100000):
        self.hash_to_kangaroo = {}  # hash160_int -> (kangaroo_id, key, distance, type)
        self.max_entries = max_entries
        self.collision_lock = threading.Lock()
        
    def add_point(self, kangaroo):
        """Fügt einen Punkt zur Kollisionserkennung hinzu"""
        with self.collision_lock:
            if len(self.hash_to_kangaroo) >= self.max_entries:
                # Entferne älteste Einträge (einfache FIFO)
                oldest_keys = list(self.hash_to_kangaroo.keys())[:self.max_entries // 4]
                for key in oldest_keys:
                    del self.hash_to_kangaroo[key]
            
            hash_key = kangaroo.current_hash160_int
            if hash_key in self.hash_to_kangaroo:
                # Kollision gefunden!
                existing = self.hash_to_kangaroo[hash_key]
                return {
                    'type': 'kangaroo_collision',
                    'kangaroo1': {
                        'id': existing[0],
                        'key': existing[1],
                        'distance': existing[2],
                        'type': existing[3]
                    },
                    'kangaroo2': {
                        'id': kangaroo.kangaroo_id,
                        'key': kangaroo.current_key,
                        'distance': kangaroo.distance,
                        'type': kangaroo.kangaroo_type
                    },
                    'hash160': hash_key
                }
            else:
                # Füge neuen Punkt hinzu
                self.hash_to_kangaroo[hash_key] = (
                    kangaroo.kangaroo_id,
                    kangaroo.current_key,
                    kangaroo.distance,
                    kangaroo.kangaroo_type
                )
                return None

def kangaroo_worker(worker_id, range_start, range_end, target_hash160, jump_table, 
                   num_kangaroos_per_worker, results_queue, stop_event):
    """Worker-Prozess für Kangaroo-Suche"""
    print(f"Shinobi Work {worker_id} gestartet mit {num_kangaroos_per_worker} Kangaroos")
    
    # Erstelle Kangaroos für diesen Worker
    kangaroos = []
    collision_detector = KangarooCollisionDetector()
    
    for i in range(num_kangaroos_per_worker):
        kangaroo_type = 'tame' if i % 2 == 0 else 'wild'
        kangaroo = Hash160Kangaroo(
            range_start, range_end, target_hash160, jump_table,
            f"{worker_id}-{i}", kangaroo_type
        )
        kangaroos.append(kangaroo)
    
    iterations = 0
    start_time = time.time()
    last_report = start_time
    
    try:
        while not stop_event.is_set():
            for kangaroo in kangaroos:
                if stop_event.is_set():
                    break
                
                # Mache Sprung
                kangaroo.make_jump()
                iterations += 1
                
                # Prüfe Ziel-Kollision
                target_match = kangaroo.check_target_collision()
                if target_match:
                    results_queue.put(target_match)
                    if target_match['type'] == 'exact_match':
                        stop_event.set()
                        return
                
                # Prüfe Kangaroo-Kollisionen
                collision = collision_detector.add_point(kangaroo)
                if collision:
                    results_queue.put(collision)
                
                # Periodische Berichte
                current_time = time.time()
                if current_time - last_report > 1:  # Alle 30 Sekunden
                    elapsed = current_time - start_time
                    rate = iterations / elapsed if elapsed > 0 else 0
                    results_queue.put({
                        'type': 'progress_report',
                        'worker_id': worker_id,
                        'iterations': iterations,
                        'rate': rate,
                        'elapsed': elapsed,
                        'kangaroos': len(kangaroos)
                    })
                    last_report = current_time
                
    except KeyboardInterrupt:
        print(f"Shinobi Work {worker_id} gestoppt")
    except Exception as e:
        results_queue.put({
            'type': 'error',
            'worker_id': worker_id,
            'error': str(e)
        })


def hash160_kangaroo_search(range_start, range_end, target_address, num_workers=2, 
                          kangaroos_per_worker=3, max_runtime=999999):
    """Hauptfunktion für Hash160-Kangaroo-Suche"""
    
    target_hash160 = get_target_hash160(target_address)
    if not target_hash160:
        print("❌  False Hash160 nicht extrahieren!")
        return False
    
    print(f"\n🦘 Hash160-Kangaroo-Suche gestartet:")
    print(f"   Ziel: {target_address}")
    print(f"   Hash160: {target_hash160.hex()}")
    print(f"   Bereich: {hex(range_start)} - {hex(range_end)}")
    print(f"   Bereichsgröße: 2^{(range_end - range_start).bit_length()-1}")
    print(f"   Worker: {num_workers}")
    print(f"   Kangaroos pro Worker: {kangaroos_per_worker}")
    print(f"   Gesamt Kangaroos: {num_workers * kangaroos_per_worker}")
    print(f"   Max. Laufzeit: {max_runtime}s")
    
    # Erstelle Jump-Tabelle
    jump_table = get_jump_table()
    print(f"   Jump-Tabelle: {len(jump_table)} Einträge")
    
    # Erstelle Queues und Events
    results_queue = multiprocessing.Queue()
    stop_event = multiprocessing.Event()
    
    # Starte Worker-Prozesse
    processes = []
    for worker_id in range(num_workers):
        p = multiprocessing.Process(
            target=kangaroo_worker,
            args=(worker_id, range_start, range_end, target_hash160, jump_table,
                 kangaroos_per_worker, results_queue, stop_event)
        )
        p.start()
        processes.append(p)
    
    # Sammle Ergebnisse
    start_time = time.time()
    total_iterations = 0
    total_collisions = 0
    total_findings = []
    found_target = False
    
    print(f"\nShinobi spring...")
    
    try:
        while time.time() - start_time < max_runtime and not found_target:
            try:
                result = results_queue.get(timeout=1)
                
                if result['type'] == 'exact_match':
                    print(f"\n🎯🎯🎯 ZIELADRESSE EXAKT GEFUNDEN!")
                    print(f"   Key: {result['key']}")
                    print(f"   Adresse: {result['address']}")
                    print(f"   Hash160: {result['hash160']}")
                    print(f"   Kangaroo: {result['kangaroo_id']} ({result['kangaroo_type']})")
                    print(f"   Distanz: {result['distance']:,}")
                    
                    # Speichere Treffer
                    with open("kangaroo_hits.txt", "a") as f:
                        f.write(f"EXACT: {result['key']} {result['address']} {result['hash160']}\n")
                    
                    found_target = True
                    stop_event.set()
                    
                elif result['type'] == 'prefix_match':
                    print(f"🎯 Präfix-Match gefunden!")
                    print(f"   Key: {result['key']}")
                    print(f"   Adresse: {result['address']}")
                    print(f"   Hash160: {result['hash160']}")
                    print(f"   Kangaroo: {result['kangaroo_id']} ({result['kangaroo_type']})")
                    total_findings.append(result)
                    
                    with open("kangaroo_prefix_hits.txt", "a") as f:
                        f.write(f"PREFIX: {result['key']} {result['address']} {result['hash160']}\n")
                
                elif result['type'] == 'kangaroo_collision':
                    total_collisions += 1 
                    
                elif result['type'] == 'progress_report':
                    total_iterations += result['iterations']
                    elapsed_minutes = int(result['elapsed'] // 60)
                    elapsed_seconds = int(result['elapsed'] % 60)
                    print(f"\r📊 Fortschritt [{elapsed_minutes}m {elapsed_seconds}s]: "
                          f"{total_iterations:,} Sprünge, "
                          f"{int(result['rate']):,}/s, "
                          f"Kollisionen: {total_collisions}, "
                          f"Prefix-Matches: {len(total_findings)}", end='', flush=True)
                
                elif result['type'] == 'error':
                    print(f"❌ Worker {result['worker_id']} Fehler: {result['error']}")
                
            except queue.Empty:
                continue
            except KeyboardInterrupt:
                print(f"\n⏹️ Suche durch Benutzer gestoppt")
                break
                
    except KeyboardInterrupt:
        print(f"\n⏹️ Suche durch Benutzer gestoppt")
    
    # Stoppe alle Prozesse
    stop_event.set()
    for p in processes:
        p.join(timeout=5)
        if p.is_alive():
            p.terminate()
    
    elapsed = time.time() - start_time
    print(f"\n📊 Kangaroo-Suche beendet:")
    print(f"   Laufzeit: {elapsed:.2f}s")
    print(f"   Geschätzte Sprünge: {total_iterations:,}")
    print(f"   Präfix-Matches: {len(total_findings)}")
    print(f"   Ziel gefunden: {'✅ JA' if found_target else '❌ NEIN'}")
    
    return found_target

def analyze_and_kangaroo_search(filename, target_prefix='1PWo3', target_address=None, 
                               num_workers=2, kangaroos_per_worker=3):
    """Analysiert Sprungbretter und startet Kangaroo-Suche"""
    
    print(f"🔍 Lade Sprungbretter aus {filename} für Präfix '{target_prefix}'...")
    private_keys_with_prefix = []
    
    try:
        with open(filename, "r") as f:
            for line in f:
                if not line.strip():
                    continue
                parts = line.strip().split('\t')
                if len(parts) != 2:
                    continue
                
                original_addr, hexkey = parts
                if not original_addr.startswith(target_prefix):
                    continue
                    
                if re.match(r'^[0-9a-fA-F]{64}$', hexkey):
                    try:
                        private_key_int = int(hexkey, 16)
                        private_keys_with_prefix.append(private_key_int)
                    except:
                        continue
    except FileNotFoundError:
        print(f"❌ Datei '{filename}' nicht gefunden!")
        return
    
    if not private_keys_with_prefix:
        print(f"❌ Keine Sprungbretter mit Präfix '{target_prefix}' gefunden!")
        return
    
    private_keys_with_prefix.sort()
    print(f"✅ {len(private_keys_with_prefix)} Sprungbretter geladen")
    
    # Bestimme Suchbereich basierend auf Sprungbrettern
    min_key = min(private_keys_with_prefix)
    max_key = max(private_keys_with_prefix)
    range_size = max_key - min_key
    
    # Erweitere Bereich für Kangaroo-Suche
    extension = max(range_size, 2**20)  # Mindestens 1M Extension
    range_start = min_key
    range_end = max_key 
    
    print(f"   Sprungbrett-Bereich: {hex(min_key)} - {hex(max_key)}")
    print(f"   Kangaroo-Suchbereich: {hex(range_start)} - {hex(range_end)}")
    print(f"   Erweiterung: {extension:,}")
    
    if target_address:
        success = hash160_kangaroo_search(
            range_start, range_end, target_address, 
            num_workers, kangaroos_per_worker
        )
        if success:
            print(f"🎉 ERFOLGREICH! Ziel gefunden!")
        else:
            print(f"💔 Ziel nicht gefunden")
    else:
        print(f"⚠️ Keine Zieladresse angegeben")

if __name__ == "__main__":
    # Definiere die Parameter für die Suche
    range_start = 2**70  # Start des Suchbereichs
    range_end = 2**71 - 1  # Ende des Suchbereichs
    target_address = "1PWo3JeB9jrGwfHDNpdGK54CRas7fsVzXU"  # Zieladresse
    num_workers = multiprocessing.cpu_count()  # Anzahl der CPU-Kerne
    kangaroos_per_worker = 3  # Kangaroos pro Worker
    
    print(f"🦘 Starte Hash160-Kangaroo-Suche:")
    print(f"   CPU-Kerne: {num_workers}")
    print(f"   Kangaroos pro Worker: {kangaroos_per_worker}")
    print(f"   Gesamt Kangaroos: {num_workers * kangaroos_per_worker}")
    
    # Starte die Kangaroo-Suche direkt
    success = hash160_kangaroo_search(
        range_start, range_end, target_address, 
        num_workers, kangaroos_per_worker
    )
    
    if success:
        print(f"🎉 Jangan Lupa Ngopi")
    else:
        print(f"Author Shinobi")
    
    analyze_and_kangaroo_search(file, prefix, target, num_workers, kangaroos_per_worker)