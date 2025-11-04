#!/usr/bin/env python3
"""
Boss Fight System for Velmira Game
Implements the "Abandoned Animals (Part 1)" scenario
"""

import json
import random
from typing import Dict, List, Tuple, Optional
from enum import Enum


__all__ = ['BuffType', 'Unit', 'BossFight', 'main']


class BuffType(Enum):
    """Types of buffs and debuffs"""
    BLEEDING = "bleeding"
    AGILITY = "agility"
    FEAR = "fear"
    MOCKERY = "mockery"
    VIOLENCE = "violence"
    STUNNED = "stunned"


class Unit:
    """Represents a unit in the game"""
    
    def __init__(self, unit_data: Dict):
        self.id = unit_data.get("id")
        self.name = unit_data.get("name")
        self.position = tuple(unit_data.get("position", [0, 0]))
        self.level = unit_data.get("level", 1)
        
        stats = unit_data.get("stats", {})
        self.max_hp = stats.get("hp", 100)
        self.hp = self.max_hp
        self.max_sp = stats.get("sp", 50)
        self.sp = self.max_sp
        self.sp_mechanics = stats.get("sp_mechanics", {})
        
        self.passive_abilities = unit_data.get("passive_abilities", [])
        self.abilities = unit_data.get("abilities", [])
        self.buffs = {}
        self.is_stunned = False
        
    def take_damage(self, damage: int, attacker: Optional['Unit'] = None) -> int:
        """Apply damage to the unit, considering buffs and passives"""
        actual_damage = damage
        
        # Check if stunned - take 2x damage
        if self.is_stunned:
            actual_damage *= 2
        
        # Apply damage reduction from passives
        if attacker:
            for passive in self.passive_abilities:
                if passive.get("id") == "special_person":
                    effect = passive.get("effect", {})
                    if effect.get("target") == attacker.id:
                        reduction = effect.get("reduction", 0)
                        actual_damage *= (1 - reduction)
        
        self.hp = max(0, self.hp - int(actual_damage))
        return int(actual_damage)
    
    def restore_sp(self, amount: int):
        """Restore SP"""
        self.sp = min(self.max_sp, self.sp + amount)
    
    def lose_sp(self, amount: int):
        """Lose SP"""
        self.sp = max(0, self.sp - amount)
        
        # Check if SP reached 0
        if self.sp == 0 and self.sp_mechanics.get("stun_at_zero"):
            self.is_stunned = True
            print(f"{self.name} 已经眩晕! SP耗尽!")
    
    def apply_buff(self, buff_type: BuffType, stacks: int = 1):
        """Apply a buff or debuff"""
        if buff_type.value not in self.buffs:
            self.buffs[buff_type.value] = 0
        self.buffs[buff_type.value] += stacks
        print(f"{self.name} 获得 {stacks} 层 {buff_type.value}!")
    
    def remove_buff(self, buff_type: BuffType, stacks: int = 1):
        """Remove buff stacks"""
        if buff_type.value in self.buffs:
            self.buffs[buff_type.value] = max(0, self.buffs[buff_type.value] - stacks)
            if self.buffs[buff_type.value] == 0:
                del self.buffs[buff_type.value]
    
    def start_turn(self):
        """Process start of turn effects"""
        # Process bleeding
        if BuffType.BLEEDING.value in self.buffs:
            bleed_stacks = self.buffs[BuffType.BLEEDING.value]
            damage = int(self.max_hp * 0.05 * bleed_stacks)
            self.hp = max(0, self.hp - damage)
            print(f"{self.name} 受到流血伤害: {damage} (层数: {bleed_stacks})")
        
        # Recover from stun
        if self.is_stunned:
            self.is_stunned = False
            self.sp = self.sp_mechanics.get("auto_restore_after_stun", self.max_sp)
            print(f"{self.name} 从眩晕中恢复! SP恢复至 {self.sp}")


class BossFight:
    """Main boss fight controller"""
    
    def __init__(self, scenario_file: str):
        """Initialize the boss fight from scenario file"""
        with open(scenario_file, 'r', encoding='utf-8') as f:
            data = json.load(f)
        
        self.scenario = data["scenario"]
        self.map_width = self.scenario["map"]["width"]
        self.map_height = self.scenario["map"]["height"]
        self.covers = self.scenario["map"]["covers"]
        
        # Initialize boss
        boss_data = self.scenario["units"]["boss"]
        self.boss = Unit(boss_data)
        
        # Initialize player units
        self.player_units = []
        for unit_data in self.scenario["units"]["player_units"]:
            self.player_units.append(Unit(unit_data))
        
        self.victory_hp_threshold = self.scenario["victory_condition"]["hp_threshold"]
        self.turn = 0
    
    def calculate_damage_with_passives(self, attacker: Unit, base_damage: int, 
                                      target: Unit) -> int:
        """Calculate damage considering all passive abilities"""
        damage = base_damage
        
        # Hot-headed passive (75% chance for 75% extra damage)
        for passive in attacker.passive_abilities:
            if passive.get("id") == "hot_headed":
                effect = passive.get("effect", {})
                if random.random() < effect.get("chance", 0):
                    multiplier = effect.get("damage_multiplier", 1.0)
                    damage *= multiplier
                    print(f"热血上头触发! 伤害增加至 {int(damage)}")
        
        # Survival of the Fittest (10% extra damage per bleeding stack)
        for passive in attacker.passive_abilities:
            if passive.get("id") == "survival_of_fittest":
                if BuffType.BLEEDING.value in target.buffs:
                    bleed_stacks = target.buffs[BuffType.BLEEDING.value]
                    bonus = effect.get("damage_per_stack", 0.10) * bleed_stacks
                    damage *= (1 + bonus)
                    print(f"弱肉强食触发! 因流血层数 {bleed_stacks} 增加伤害")
        
        # Violence buff (2x damage on first stage)
        if BuffType.VIOLENCE.value in attacker.buffs:
            damage *= 2
            attacker.lose_sp(10)
            attacker.remove_buff(BuffType.VIOLENCE, 1)
            print(f"暴力buff触发! 伤害翻倍但消耗10 SP")
        
        return int(damage)
    
    def apply_attack_effects(self, attacker: Unit, target: Unit, 
                           ability: Dict, stage_index: int = 0):
        """Apply effects after an attack"""
        # Bloodthirsty Shovel - apply bleeding
        for passive in attacker.passive_abilities:
            if passive.get("id") == "bloodthirsty_shovel":
                target.apply_buff(BuffType.BLEEDING, 1)
        
        # Abandoned Animal passive - 25% chance to lose 5 SP
        for passive in attacker.passive_abilities:
            if passive.get("id") == "abandoned_animal":
                effect = passive.get("effect", {})
                if random.random() < effect.get("chance", 0):
                    sp_loss = effect.get("sp_amount", 5)
                    attacker.lose_sp(sp_loss)
                    print(f"被遗弃的动物触发! {attacker.name} 失去 {sp_loss} SP")
    
    def check_victory_condition(self) -> bool:
        """Check if victory condition is met"""
        if self.boss.hp <= self.victory_hp_threshold:
            print(f"\n战斗结束! {self.boss.name} 的HP降至 {self.boss.hp}")
            print("进入剧情...")
            return True
        return False
    
    def display_status(self):
        """Display current battle status"""
        print(f"\n=== 回合 {self.turn} ===")
        print(f"{self.boss.name}: HP {self.boss.hp}/{self.max_hp} | SP {self.boss.sp}/{self.boss.max_sp}")
        if self.boss.buffs:
            print(f"  Buffs: {self.boss.buffs}")
        
        for unit in self.player_units:
            print(f"{unit.name} (Lv.{unit.level}): 位置 {unit.position}")
    
    def run(self):
        """Main game loop"""
        print(f"=== {self.scenario['name']} ===")
        print(f"地图大小: {self.map_width}x{self.map_height}")
        print(f"\n战斗开始!")
        
        while True:
            self.turn += 1
            self.display_status()
            
            # Boss turn
            self.boss.start_turn()
            
            # Check victory
            if self.check_victory_condition():
                break
            
            # Player turns would go here
            # (Simplified for demonstration)
            
            # Check for game over conditions
            if self.boss.hp <= 0:
                print(f"\n{self.boss.name} 被击败!")
                break


def main():
    """
    Main entry point for the Velmira Boss Fight System.
    
    This function initializes and displays information about the boss fight scenario.
    It loads the scenario data from the JSON file and prepares the battle system.
    
    Returns:
        int: Exit code (0 for success, 1 for error)
    """
    print("Velmira Boss Fight System")
    print("=" * 50)
    
    try:
        fight = BossFight("abandoned_animals_pt1.json")
        print(f"\n已加载场景: {fight.scenario['name']}")
        print(f"Boss: {fight.boss.name} - Lv.{fight.boss.level}")
        print(f"玩家单位:")
        for unit in fight.player_units:
            print(f"  - {unit.name} (Lv.{unit.level}) at {unit.position}")
        
        print("\n战斗系统已准备就绪!")
        print(f"胜利条件: 将{fight.boss.name}的HP降至{fight.victory_hp_threshold}")
        
        return 0
        
    except FileNotFoundError:
        print("错误: 找不到场景文件 'abandoned_animals_pt1.json'")
        return 1
    except Exception as e:
        print(f"错误: {e}")
        return 1


if __name__ == "__main__":
    import sys
    sys.exit(main())
