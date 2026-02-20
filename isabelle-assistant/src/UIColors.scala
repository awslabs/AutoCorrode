/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

package isabelle.assistant

/**
 * Centralized theme-aware color constants for UI components.
 * All colors are defined as (dark theme, light theme) pairs and resolved
 * via ThemeUtils at runtime.
 * 
 * Color schemes are designed to:
 * - Provide sufficient contrast in both light and dark themes
 * - Use semantic colors (green=success, red=error, etc.)
 * - Maintain visual consistency across the plugin UI
 * - Support accessibility requirements (WCAG 2.1 AA minimum)
 */
object UIColors {

  /** Chat bubble colors for message display in the dockable panel. */
  object ChatBubble {
    def userBackground: String = ThemeUtils.themedHex("#2a3a4a", "#e8f0fe")
    def userBorder: String = ThemeUtils.themedHex("#5b9bd5", "#4285f4")
    def userTimestamp: String = ThemeUtils.themedHex("#a0a8b0", "#5f6368")
    
    def assistantBackground: String = ThemeUtils.themedHex("#302040", "#f3e8fd")
    def assistantBorder: String = ThemeUtils.themedHex("#8060b0", "#9c27b0")
    def assistantTimestamp: String = ThemeUtils.themedHex("#a0a8b0", "#5f6368")
    
    def errorBackground: String = ThemeUtils.themedHex("#4a2020", "#ffebee")
    def errorBorder: String = ThemeUtils.themedHex("#e06060", "#ef5350")
    def errorTimestamp: String = ThemeUtils.themedHex("#a0a8b0", "#5f6368")
  }
  
  // Welcome message colors
  object Welcome {
    def background: String = ThemeUtils.themedHex("#3a3520", "#fff8e1")
    def border: String = ThemeUtils.themedHex("#6a6030", "#ffe082")
    def title: String = ThemeUtils.themedHex("#d4b830", "#f57f17")
    def text: String = ThemeUtils.themedHex("#c0b890", "#555555")
    def muted: String = ThemeUtils.themedHex("#888070", "#888888")
    def codeBackground: String = ThemeUtils.themedHex("#3a3a3a", "#f0f0f0")
    def linkColor: String = ThemeUtils.themedHex("#b090d0", "#7b1fa2")
  }
  
  // Error/warning box colors
  object ErrorBox {
    def background: String = ThemeUtils.themedHex("#4a2020", "#ffebee")
    def border: String = ThemeUtils.themedHex("#804040", "#ef9a9a")
    def text: String = ThemeUtils.themedHex("#e09090", "#c62828")
  }
  
  // Help table colors
  object HelpTable {
    def headerBackground: String = if (ThemeUtils.isDark) "#3a3a3a" else "#f0f0f0"
    def borderColor: String = if (ThemeUtils.isDark) "#555" else "#ccc"
    def rowBorder: String = if (ThemeUtils.isDark) "#444" else "#eee"
    def accentColor: String = if (ThemeUtils.isDark) "#b090d0" else "#7b1fa2"
  }
  
  // Info box colors (for help sections)
  object InfoBox {
    def background: String = if (ThemeUtils.isDark) "#2a3040" else "#f5f5f5"
    def border: String = if (ThemeUtils.isDark) "#4a4a5a" else "#e0e0e0"
  }
  
  // General link color
  def linkColor: String = "#7b1fa2"
  
  // Code block colors (Rustdoc-inspired: cream background, minimal borders)
  object CodeBlock {
    def background: String = ThemeUtils.themedHex("#1e1e1e", "#f5f3f0")  // Cream/beige like Rustdoc
    def border: String = ThemeUtils.themedHex("#3a3a3a", "#e1dfdb")
    def actionBackground: String = ThemeUtils.themedHex("#2a2a2a", "#ebe9e6")
    def actionBorder: String = ThemeUtils.themedHex("#3a3a3a", "#d8d6d2")
    def actionLinkBackground: String = ThemeUtils.themedHex("#4a3a5a", "#e8e0f0")
  }
  
  // Inline code background
  def inlineCodeBackground: String = ThemeUtils.themedHex("#3a3a3a", "#f0f0f0")
  
  // Table colors
  object Table {
    def border: String = ThemeUtils.themedHex("#555", "#d0d0d0")
    def headerBackground: String = ThemeUtils.themedHex("#3a3a3a", "#f0f0f0")
  }
  
  // Tool message colors (for tool-use display in chat)
  object ToolMessage {
    def background: String = ThemeUtils.themedHex("#203a3a", "#e0f2f1")
    def border: String = ThemeUtils.themedHex("#00897b", "#00897b")
    def timestamp: String = ThemeUtils.themedHex("#a0a8b0", "#5f6368")
    def parameterBackground: String = ThemeUtils.themedHex("#2a4040", "#f0f8f7")
    def parameterBorder: String = ThemeUtils.themedHex("#00695c", "#b2dfdb")
  }
  
  // Copy button colors (subtle icon next to messages)
  object CopyButton {
    def color: String = ThemeUtils.themedHex("#888888", "#999999")
    def hoverColor: String = ThemeUtils.themedHex("#b0b0b0", "#666666")
  }
  
  // Minimal button styling for Insert/Copy (Rustdoc-inspired: subtle, text-like)
  object CodeButton {
    def background: String = "transparent"
    def hoverBackground: String = ThemeUtils.themedHex("#3a3a3a", "#e8e6e3")
    def border: String = ThemeUtils.themedHex("#4a4a4a", "#d0cec9")
    def text: String = ThemeUtils.themedHex("#c0c0c0", "#3c4043")
  }
  
  // Status indicator colors (for colored dots)
  object StatusDot {
    def ready: String = ThemeUtils.themedHex("#81c784", "#4caf50")
    def busy: String = ThemeUtils.themedHex("#ffb74d", "#ff9800")
    def error: String = ThemeUtils.themedHex("#e57373", "#f44336")
  }
  
  // Top panel button styling
  object TopButton {
    def background: String = ThemeUtils.themedHex("#3a3a3a", "#f0f0f0")
    def hoverBackground: String = ThemeUtils.themedHex("#4a4a4a", "#e0e0e0")
    def border: String = ThemeUtils.themedHex("#555555", "#cccccc")
  }
  
  // Light-tinted badge styling (modern approach: light bg + colored text + thin border)
  object Badge {
    // Success/verified
    def successBackground: String = ThemeUtils.themedHex("#1b3a1f", "#e8f5e9")
    def successText: String = ThemeUtils.themedHex("#81c784", "#2e7d32")
    def successBorder: String = ThemeUtils.themedHex("#4caf50", "#81c784")
    
    // Error/failed
    def errorBackground: String = ThemeUtils.themedHex("#3a1a1a", "#ffebee")
    def errorText: String = ThemeUtils.themedHex("#e57373", "#c62828")
    def errorBorder: String = ThemeUtils.themedHex("#f44336", "#ef9a9a")
    
    // Warning/unverified
    def warningBackground: String = ThemeUtils.themedHex("#3a2a10", "#fff8e1")
    def warningText: String = ThemeUtils.themedHex("#ffb74d", "#f57f17")
    def warningBorder: String = ThemeUtils.themedHex("#ff9800", "#ffb74d")
    
    // Info/sledgehammer
    def infoBackground: String = ThemeUtils.themedHex("#1a2a3a", "#e3f2fd")
    def infoText: String = ThemeUtils.themedHex("#64b5f6", "#1565c0")
    def infoBorder: String = ThemeUtils.themedHex("#2196f3", "#64b5f6")
    
    // Neutral/verifying
    def neutralBackground: String = ThemeUtils.themedHex("#2a2a2a", "#f5f5f5")
    def neutralText: String = ThemeUtils.themedHex("#bdbdbd", "#616161")
    def neutralBorder: String = ThemeUtils.themedHex("#9e9e9e", "#bdbdbd")
    
    // Accent/eisbach missing
    def accentBackground: String = ThemeUtils.themedHex("#3a2010", "#fbe9e7")
    def accentText: String = ThemeUtils.themedHex("#ff8a65", "#d84315")
    def accentBorder: String = ThemeUtils.themedHex("#ff5722", "#ff8a65")
  }
  
  // Chat input box styling (modern, clean look)
  object ChatInput {
    def background: String = ThemeUtils.themedHex("#2a2a2a", "#ffffff")
    def border: String = ThemeUtils.themedHex("#4a4a4a", "#d0d0d0")
    def focusBorder: String = ThemeUtils.themedHex("#8060b0", "#7b1fa2")
    def placeholder: String = ThemeUtils.themedHex("#666666", "#9e9e9e")
    def sendButton: String = ThemeUtils.themedHex("#888888", "#9e9e9e")
    def sendButtonHover: String = ThemeUtils.themedHex("#b090d0", "#7b1fa2")
    def sendButtonHoverBackground: String = ThemeUtils.themedHex("#3a3a4a", "#f0e8f8")
  }
  
  // Ask user widget colors (matches assistant message aesthetic with amber accent)
  object AskUser {
    // Card container - white background like other message bubbles
    def background: String = "white"
    def border: String = ThemeUtils.themedHex("#d4a020", "#f5a623")  // Amber left border
    
    // Title ("Assistant needs your input")
    def title: String = ThemeUtils.themedHex("#a0a8b0", "#5f6368")  // Same as message timestamps
    
    // Question text
    def questionText: String = ThemeUtils.themedHex("#ffffff", "#333333")  // Main text color
    
    // Context subtitle
    def contextText: String = ThemeUtils.themedHex("#a0a8b0", "#777777")  // Muted
    
    // Option buttons - subtle styling
    def optionBackground: String = ThemeUtils.themedHex("#3a3a3a", "#f8f8f8")
    def optionBorder: String = ThemeUtils.themedHex("#555555", "#e0e0e0")
    def optionText: String = ThemeUtils.themedHex("#d0d0d0", "#444444")
    def optionLetter: String = ThemeUtils.themedHex("#d4a020", "#f5a623")  // Amber accent
    
    // Hover state
    def optionHoverBackground: String = ThemeUtils.themedHex("#454545", "#eeeeee")
  }
  
  // Task list widget colors (blue accent for task/work semantics)
  object TaskList {
    // Card container - white background like other message bubbles
    def background: String = "white"
    def border: String = ThemeUtils.themedHex("#1565c0", "#1976d2")  // Blue left border
    
    // Header text ("Task List")
    def headerText: String = ThemeUtils.themedHex("#64b5f6", "#1565c0")
    
    // Progress subtitle ("3/6 done")
    def progressText: String = ThemeUtils.themedHex("#90a4ae", "#78909c")
    
    // Status icons
    def doneIcon: String = ThemeUtils.themedHex("#81c784", "#4caf50")      // ✓ green
    def pendingIcon: String = ThemeUtils.themedHex("#90a4ae", "#78909c")   // ○ grey
    def nextIcon: String = ThemeUtils.themedHex("#64b5f6", "#1976d2")      // ● blue
    def irrelevantIcon: String = ThemeUtils.themedHex("#616161", "#9e9e9e") // ✗ muted
    
    // Text colors
    def irrelevantText: String = ThemeUtils.themedHex("#616161", "#9e9e9e") // strikethrough text
    def labelColor: String = ThemeUtils.themedHex("#b0bec5", "#607d8b")     // "Description:" labels
    def taskText: String = ThemeUtils.themedHex("#e0e0e0", "#333333")       // Task title/description
  }
  
  
  // Syntax highlighting colors for Isabelle code blocks (Rustdoc-inspired, subtle)
  object Syntax {
    // Keywords (lemma, theorem, proof, etc.) - muted purple/mauve like Rustdoc
    def keyword: String = ThemeUtils.themedHex("#b392f0", "#8250df")
    
    // Types (nat, bool, list, etc.) - subtle teal
    def typeColor: String = ThemeUtils.themedHex("#79c0ff", "#0550ae")
    
    // Comments (*...*) - soft grey
    def comment: String = ThemeUtils.themedHex("#8b949e", "#57606a")
    
    // String literals "..." - soft green
    def stringLiteral: String = ThemeUtils.themedHex("#a5d6ff", "#0a3069")
  }
}
