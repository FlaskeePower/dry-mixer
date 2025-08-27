# Dry Mixer — легкий міксер відео (tkinter/ttk)
# by kremsalkin

import json, os, sys, random, shutil, subprocess, threading, time
from pathlib import Path
from queue import Queue, Empty

import tkinter as tk
from tkinter import filedialog, messagebox, ttk

DEFAULT_DURATION = "01:00:00"
DEFAULT_CRF = 18
DEFAULT_ABR = "160k"
LOG_POLL_MS = 80

# ---------- Утиліти ----------
def have_ffmpeg():
    try:
        subprocess.run(["ffmpeg","-version"], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        subprocess.run(["ffprobe","-version"], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        return True
    except Exception:
        return False

def parse_duration(s: str) -> int:
    s = (s or "").strip()
    if not s: return 0
    p = [int(x) for x in s.split(":")]
    if   len(p)==1: h,m,sec = 0,0,p[0]
    elif len(p)==2: h,m,sec = 0,p[0],p[1]
    else:           h,m,sec = p[-3],p[-2],p[-1]
    return h*3600 + m*60 + sec

def ffprobe_duration(p: Path) -> float:
    try:
        out = subprocess.check_output(
            ["ffprobe","-v","error","-show_entries","format=duration",
             "-of","default=nokey=1:noprint_wrappers=1", str(p)], text=True)
        return float(out.strip())
    except Exception:
        return 0.0

# ---------- Шафл ----------
def shuffle_full(items):
    items=list(items); random.shuffle(items); return items

def infer_block_size(items):
    n=len(items)
    if n==0: return 0
    for k in range(1, min(n,500)+1):
        if n%k==0 and items[:k]*(n//k)==items: return k
    seen=set()
    for i,x in enumerate(items,1):
        if x in seen: return i-1 if i>1 else n
        seen.add(x)
    return n

def shuffle_blockwise_no_seam(items, bsz):
    if bsz<=0: return shuffle_full(items)
    out=[]; prev=None
    for i in range(0,len(items),bsz):
        block=items[i:i+bsz]; random.shuffle(block)
        if prev is not None and block and block[0]==prev:
            for j in range(1,len(block)):
                if block[j]!=prev: block[0],block[j]=block[j],block[0]; break
        out.extend(block); prev = block[-1] if block else None
    return out

def enforce_no_adjacent_duplicates(seq):
    seq=list(seq); n=len(seq)
    for i in range(1,n):
        if seq[i]==seq[i-1]:
            for j in range(i+1,n):
                if seq[j]!=seq[i-1]: seq[i],seq[j]=seq[j],seq[i]; break
    return seq

# ---------- Додаток ----------
class App:
    def __init__(self, root: tk.Tk):
        root.title("Dry Mixer")
        root.geometry("1140x700")
        root.minsize(900,560)
        self.root=root

        style=ttk.Style()
        try: style.theme_use("clam")
        except: pass
        style.configure("Border.TButton", padding=6, relief="raised", borderwidth=2)
        style.map("Border.TButton", relief=[("pressed","sunken")], background=[("active","#e0e4ff")])

        self.log_q=Queue(); self.worker=None; self.block_size=None
        self.stop_flag=threading.Event(); self.current_proc=None
        self.running=False; self.start_ts=None

        # ------- Ліва (фіксована) -------
        left=ttk.Frame(root, padding=8); left.pack(side=tk.LEFT, fill=tk.Y)

        lf=ttk.LabelFrame(left, text="Вхідні кліпи"); lf.pack(fill=tk.Y)
        cont=ttk.Frame(lf, padding=6); cont.pack(fill=tk.BOTH, expand=True)
        self.listbox=tk.Listbox(cont, selectmode=tk.EXTENDED, width=58, height=28, activestyle="none")
        sb=ttk.Scrollbar(cont, orient=tk.VERTICAL, command=self.listbox.yview)
        self.listbox.configure(yscrollcommand=sb.set)
        self.listbox.grid(row=0,column=0,sticky="nsew"); sb.grid(row=0,column=1,sticky="ns")
        cont.columnconfigure(0,weight=1); cont.rowconfigure(0,weight=1)

        # Drag&Drop reorder
        self._drag_data={"idx":None}
        self.listbox.bind("<ButtonPress-1>", self._on_lb_press)
        self.listbox.bind("<B1-Motion>", self._on_lb_motion)
        self.listbox.bind("<ButtonRelease-1>", self._on_lb_release)

        r=ttk.Frame(left,padding=(0,6)); r.pack(fill=tk.X)
        ttk.Button(r,text="➕ Додати файли",style="Border.TButton",command=self.add_files).pack(side=tk.LEFT)
        ttk.Button(r,text="🗑 Видалити",style="Border.TButton",command=self.remove_sel).pack(side=tk.LEFT,padx=6)
        ttk.Button(r,text="♻️ Очистити",style="Border.TButton",command=self.clear_all).pack(side=tk.LEFT)

        r=ttk.Frame(left,padding=(0,6)); r.pack(fill=tk.X)
        ttk.Label(r,text="Дублювати вибране ×").pack(side=tk.LEFT)
        self.dup_sel=ttk.Spinbox(r,from_=2,to=1000,width=6); self.dup_sel.delete(0,tk.END); self.dup_sel.insert(0,"3")
        self.dup_sel.pack(side=tk.LEFT,padx=4)
        ttk.Button(r,text="× Дублювати вибране",style="Border.TButton",
                   command=self.duplicate_selected).pack(side=tk.LEFT,padx=6)

        r=ttk.Frame(left,padding=(0,6)); r.pack(fill=tk.X)
        ttk.Label(r,text="Дублювати ВЕСЬ список ×").pack(side=tk.LEFT)
        self.dup_all=ttk.Spinbox(r,from_=2,to=1000,width=6); self.dup_all.delete(0,tk.END); self.dup_all.insert(0,"3")
        self.dup_all.pack(side=tk.LEFT,padx=4)
        ttk.Button(r,text="× Дублювати список",style="Border.TButton",
                   command=self.duplicate_all).pack(side=tk.LEFT,padx=6)

        modef=ttk.LabelFrame(left,text="Режим перемішування"); modef.pack(fill=tk.X,pady=6)
        self.shuffle_mode=tk.StringVar(value="full")
        ttk.Radiobutton(modef,text="Повний рандом",variable=self.shuffle_mode,value="full").pack(anchor='w')
        ttk.Radiobutton(modef,text="Рандом блоками (з антишовом)",variable=self.shuffle_mode,value="block").pack(anchor='w')
        self.block_lbl=ttk.Label(modef,text="Розмір блока: (авто)"); self.block_lbl.pack(anchor='w',pady=(4,6))
        ttk.Button(modef,text="Перемішати зараз",style="Border.TButton",command=self.do_shuffle_now).pack(anchor='w')

        self.autofill=tk.IntVar(value=1)
        ttk.Checkbutton(left,text="Автозаповнення списку до цільової тривалості",variable=self.autofill)\
            .pack(anchor='w',pady=8)

        # ------- Права (скрол) -------
        right_canvas = tk.Canvas(root, highlightthickness=0)
        right_vscroll = ttk.Scrollbar(root, orient="vertical", command=right_canvas.yview)
        right_canvas.configure(yscrollcommand=right_vscroll.set)

        right = ttk.Frame(right_canvas, padding=8)
        right_window = right_canvas.create_window((0,0), window=right, anchor="nw")

        def _on_right_configure(event=None):
            right_canvas.configure(scrollregion=right_canvas.bbox("all"))
        right.bind("<Configure>", _on_right_configure)

        def _on_canvas_configure(event):
            right_canvas.itemconfig(right_window, width=event.width)
        right_canvas.bind("<Configure>", _on_canvas_configure)

        right_vscroll.pack(side=tk.RIGHT, fill=tk.Y)
        right_canvas.pack(side=tk.RIGHT, fill=tk.BOTH, expand=True)

        def _on_mousewheel(event):
            if event.num==5 or event.delta<0: right_canvas.yview_scroll(1,"units")
            elif event.num==4 or event.delta>0: right_canvas.yview_scroll(-1,"units")
        def _bind(_):
            right_canvas.bind_all("<MouseWheel>",_on_mousewheel)
            right_canvas.bind_all("<Button-4>",_on_mousewheel)
            right_canvas.bind_all("<Button-5>",_on_mousewheel)
        def _unbind(_):
            right_canvas.unbind_all("<MouseWheel>")
            right_canvas.unbind_all("<Button-4>")
            right_canvas.unbind_all("<Button-5>")
        right_canvas.bind("<Enter>",_bind); right_canvas.bind("<Leave>",_unbind)

        # ---- Контент праворуч ----
        r=ttk.Frame(right); r.pack(fill=tk.X)
        ttk.Label(r,text="Тривалість:").pack(side=tk.LEFT)
        self.dur_entry=ttk.Entry(r,width=10); self.dur_entry.insert(0,DEFAULT_DURATION); self.dur_entry.pack(side=tk.LEFT)
        self.fixed_duration=tk.IntVar(value=1)
        ttk.Checkbutton(r,text="Фіксована тривалість",variable=self.fixed_duration)\
            .pack(side=tk.LEFT,padx=8)
        ttk.Label(r,text=" (H:MM:SS або MM:SS)").pack(side=tk.LEFT)

        row2=ttk.LabelFrame(right,text="Вихідний файл"); row2.pack(fill=tk.X,pady=6)
        ttk.Label(row2,text="Шлях:").pack(side=tk.LEFT,padx=(6,4))
        self.out_entry=ttk.Entry(row2,width=62); self.out_entry.insert(0,"output.mp4"); self.out_entry.pack(side=tk.LEFT,pady=6)
        ttk.Button(row2,text="…",style="Border.TButton",command=self.pick_outfile).pack(side=tk.LEFT,padx=8)
        ttk.Button(row2,text="Відкрити папку",style="Border.TButton",
                   command=self.open_output_folder).pack(side=tk.LEFT,padx=6)

        # Пакетна збірка
        batchf=ttk.LabelFrame(right,text="Пакетна збірка"); batchf.pack(fill=tk.X,pady=(0,6))
        ttk.Label(batchf,text="Кількість компіляцій:").pack(side=tk.LEFT,padx=(8,4))
        self.batch_spin=ttk.Spinbox(batchf,from_=1,to=100,width=6)
        self.batch_spin.delete(0,tk.END); self.batch_spin.insert(0,"1")
        self.batch_spin.pack(side=tk.LEFT,padx=(0,12))
        self.batch_shuffle=tk.IntVar(value=1)
        ttk.Checkbutton(batchf,text="Перемішувати перед кожною",variable=self.batch_shuffle)\
            .pack(side=tk.LEFT)

        simplef=ttk.Frame(right); simplef.pack(fill=tk.X,pady=4)
        self.same_params=tk.IntVar(value=0)
        ttk.Checkbutton(simplef,
            text="Кліпи вже у єдиному форматі (залишати оригінальні параметри, сховати налаштування)",
            variable=self.same_params, command=self.toggle_video_params).pack(anchor='w')

        self.vidf=ttk.LabelFrame(right,text="Відео параметри"); self.vidf.pack(fill=tk.X,pady=6)
        rv1=ttk.Frame(self.vidf); rv1.pack(fill=tk.X,padx=6,pady=(6,2))
        ttk.Label(rv1,text="Роздільна здатність:").pack(side=tk.LEFT)
        self.res_preset=tk.StringVar(value="Оригінал")
        ttk.OptionMenu(rv1,self.res_preset,"Оригінал","Оригінал","1280x720","1920x1080","2560x1440","3840x2160")\
            .pack(side=tk.LEFT,padx=6)
        rv2=ttk.Frame(self.vidf); rv2.pack(fill=tk.X,padx=6,pady=(2,6))
        ttk.Label(rv2,text="FPS:").pack(side=tk.LEFT)
        self.fps_choice=tk.StringVar(value="Оригінал")
        ttk.OptionMenu(rv2,self.fps_choice,"Оригінал","Оригінал","24","25","30","50","60").pack(side=tk.LEFT,padx=6)
        rv3=ttk.Frame(self.vidf); rv3.pack(fill=tk.X,padx=6,pady=(0,8))
        self.quick_copy=tk.IntVar(value=0)
        ttk.Checkbutton(rv3,text="Швидкий (без перекодування, якщо можливо)",variable=self.quick_copy)\
            .pack(anchor='w')

        self.codec_f=ttk.LabelFrame(right,text="Кодек та прискорення"); self.codec_f.pack(fill=tk.X,pady=6)
        rc=ttk.Frame(self.codec_f); rc.pack(fill=tk.X,padx=6,pady=6)
        ttk.Label(rc,text="Кодек відео:").pack(side=tk.LEFT)
        self.codec_choice=tk.StringVar(value="x264 (CPU)")
        ttk.OptionMenu(rc,self.codec_choice,"x264 (CPU)",
                       "Без перекодування (copy)","x264 (CPU)","NVENC (NVIDIA)","QSV (Intel)","AMF (AMD)")\
                       .pack(side=tk.LEFT,padx=6)

        self.mode_enc=ttk.LabelFrame(right,text="Режим виходу"); self.mode_enc.pack(fill=tk.X,pady=6)
        self.out_mode=tk.StringVar(value="copy")
        ttk.Radiobutton(self.mode_enc,text="Склеїти як є (стабільне перекодування фіналу)",
                        variable=self.out_mode,value="copy").pack(anchor='w')
        ttk.Radiobutton(self.mode_enc,text="Нормалізувати кожен (→ швидкий конкат)",
                        variable=self.out_mode,value="norm").pack(anchor='w')
        ttk.Button(self.mode_enc,text="Перевірити сумісність",style="Border.TButton",
                   command=self.check_and_recommend).pack(side=tk.RIGHT,padx=8,pady=4)

        qf=ttk.LabelFrame(right,text="Якість та аудіо"); qf.pack(fill=tk.X,pady=6)
        rq1=ttk.Frame(qf); rq1.pack(fill=tk.X,padx=6,pady=(6,2))
        ttk.Label(rq1,text="CRF:").pack(side=tk.LEFT)
        self.crf=ttk.Spinbox(rq1,from_=12,to=30,width=4); self.crf.delete(0,tk.END); self.crf.insert(0,str(DEFAULT_CRF))
        self.crf.pack(side=tk.LEFT,padx=(4,16))
        ttk.Label(rq1,text="Аудіо бітрейт:").pack(side=tk.LEFT)
        self.abr=tk.StringVar(value=DEFAULT_ABR)
        ttk.OptionMenu(rq1,self.abr,"160k","128k","160k","192k","224k","256k").pack(side=tk.LEFT,padx=6)
        rq2=ttk.Frame(qf); rq2.pack(fill=tk.X,padx=6,pady=(2,6))
        ttk.Label(rq2,text="Зовнішній аудіо-файл:").pack(side=tk.LEFT)
        self.audio_entry=ttk.Entry(rq2,width=54); self.audio_entry.pack(side=tk.LEFT,padx=6)
        ttk.Button(rq2,text="Обрати…",style="Border.TButton",command=self.pick_audio).pack(side=tk.LEFT)
        self.trim_to_audio=tk.IntVar(value=0)
        ttk.Checkbutton(qf,text="Обрізати по кінцю аудіо",variable=self.trim_to_audio).pack(anchor='w',padx=6,pady=(0,8))

        logf=ttk.LabelFrame(right,text="Лог"); logf.pack(fill=tk.BOTH,expand=True,pady=6)
        self.log=tk.Text(logf,height=17,wrap=tk.WORD)
        logsb=ttk.Scrollbar(logf,orient=tk.VERTICAL,command=self.log.yview)
        self.log.configure(yscrollcommand=logsb.set)
        self.log.pack(side=tk.LEFT,fill=tk.BOTH,expand=True,padx=(6,0),pady=6)
        logsb.pack(side=tk.RIGHT,fill=tk.Y,padx=(0,6),pady=6)

        bottom=ttk.Frame(right); bottom.pack(fill=tk.X,pady=(6,0))
        ttk.Button(bottom,text="▶️ Старт",style="Border.TButton",command=self.start_clicked).pack(side=tk.LEFT)
        ttk.Button(bottom,text="⏹ Стоп",style="Border.TButton",command=self.on_stop).pack(side=tk.LEFT,padx=6)
        ttk.Button(bottom,text="🗑 Очистити логи",style="Border.TButton",command=self.clear_logs).pack(side=tk.LEFT)
        self.progress=ttk.Progressbar(bottom,mode="indeterminate",length=120); self.progress.pack(side=tk.LEFT,padx=10)
        self.status=ttk.Label(bottom,text="Готово",anchor="w"); self.status.pack(side=tk.LEFT,padx=8)
        self.elapsed_var=tk.StringVar(value="00:00")
        ttk.Label(bottom,text="⏱").pack(side=tk.LEFT,padx=(12,2))
        ttk.Label(bottom,textvariable=self.elapsed_var,anchor="w").pack(side=tk.LEFT)

        banner = """
============================================================
                        D R Y   M I X E R
============================================================

🚀 РОБІТЬ ЮТУБ!

------------------------------------------------------------
                      Допомога автору:
                 💳 4441 1144 2823 3140
                Зв'язатись: @FlaskeePower
------------------------------------------------------------
"""
        self.log_write(banner + "\n")

        def _init_scroll():
            right.update_idletasks()
            right_canvas.configure(scrollregion=right_canvas.bbox("all"))
            right_canvas.itemconfig(right_window, width=right_canvas.winfo_width())
            right_canvas.yview_moveto(0.0)
        self.root.after(0, _init_scroll)

        self.root.after(LOG_POLL_MS,self.flush_log)

    # ---------- Допоміжні ----------
    def _fmt_hhmmss(self, secs:int)->str:
        h=secs//3600; m=(secs%3600)//60; s=secs%60
        return f"{h:02d}:{m:02d}:{s:02d}" if h else f"{m:02d}:{s:02d}"

    def _tick_elapsed(self):
        if not getattr(self,"start_ts",None): return
        if self.running:
            self.elapsed_var.set(self._fmt_hhmmss(int(time.time()-self.start_ts)))
            self.root.after(500,self._tick_elapsed)

    def log_write(self,s:str): self.log.insert(tk.END,s); self.log.see(tk.END)

    def flush_log(self):
        try:
            while True: self.log_write(self.log_q.get_nowait())
        except Empty:
            pass
        finally:
            self.root.after(LOG_POLL_MS,self.flush_log)

    def set_running(self,val:bool):
        self.running=val
        if val:
            self.status.configure(text="Виконується…")
            self.start_ts=time.time(); self.elapsed_var.set("00:00"); self._tick_elapsed()
            try: self.progress.start(80)
            except: pass
        else:
            self.status.configure(text="Готово")
            self.start_ts=None; self.elapsed_var.set("00:00")
            try: self.progress.stop()
            except: pass

    def _numbered_out(self, base: Path, idx: int) -> Path:
        stem, suf = base.stem, base.suffix or ".mp4"
        return base.with_name(f"{stem}_{idx}{suf}")

    # ---------- Drag&Drop ----------
    def _on_lb_press(self,e): 
        idx=self.listbox.nearest(e.y)
        if idx>=0: self._drag_data["idx"]=idx
    def _on_lb_motion(self,e):
        fr=self._drag_data.get("idx")
        if fr is None: return
        to=self.listbox.nearest(e.y)
        if to==fr or to<0: return
        sel=list(self.listbox.curselection())
        if fr not in sel:
            it=self.listbox.get(fr); self.listbox.delete(fr)
            self.listbox.insert(to,it); self.listbox.selection_clear(0,tk.END)
            self.listbox.selection_set(to); self._drag_data["idx"]=to
        else:
            items=[self.listbox.get(i) for i in sel]
            for i in reversed(sel): self.listbox.delete(i)
            ins=self.listbox.nearest(e.y)
            for k,it in enumerate(items): self.listbox.insert(ins+k,it)
            self.listbox.selection_clear(0,tk.END)
            for k in range(len(items)): self.listbox.selection_set(ins+k)
            self._drag_data["idx"]=ins
    def _on_lb_release(self,e): self._drag_data["idx"]=None; self.update_block_label()

    # ---------- Операції зі списком ----------
    def add_files(self):
        files=filedialog.askopenfilenames(title="Виберіть відео",
              filetypes=[("MP4","*.mp4"),("Усі файли","*.*")])
        for f in files: self.listbox.insert(tk.END,f)
        self.update_block_label()

    def remove_sel(self):
        for i in reversed(self.listbox.curselection()): self.listbox.delete(i)
        self.update_block_label()

    def clear_all(self):
        self.listbox.delete(0,tk.END); self.block_size=None; self.update_block_label()

    def duplicate_selected(self):
        sel=list(self.listbox.curselection())
        if not sel: messagebox.showerror("Помилка","Вибери хоча б один елемент"); return
        n=int(self.dup_sel.get()); items=[self.listbox.get(i) for i in sel]
        for _ in range(n-1):
            for p in items: self.listbox.insert(tk.END,p)
        self.update_block_label()

    def duplicate_all(self):
        n=int(self.dup_all.get()); base=self.listbox.size()
        items=[self.listbox.get(i) for i in range(base)]
        for _ in range(n-1):
            for p in items: self.listbox.insert(tk.END,p)
        self.block_size=base; self.update_block_label()

    def update_block_label(self):
        items=[self.listbox.get(i) for i in range(self.listbox.size())]
        if self.block_size: self.block_lbl.config(text=f"Розмір блока: {self.block_size}")
        else:
            auto=infer_block_size(items) if items else 0
            self.block_lbl.config(text=f"Розмір блока: (авто={auto})")

    def do_shuffle_now(self):
        items=[self.listbox.get(i) for i in range(self.listbox.size())]
        if not items: return
        if self.shuffle_mode.get()=="block":
            bsz=self.block_size or infer_block_size(items)
            items=shuffle_blockwise_no_seam(items,bsz)
            items=enforce_no_adjacent_duplicates(items)
        else: items=shuffle_full(items)
        self.listbox.delete(0,tk.END)
        for it in items: self.listbox.insert(tk.END,it)

    # ---------- Файли/вихід/аудіо ----------
    def pick_outfile(self):
        p=filedialog.asksaveasfilename(defaultextension=".mp4",filetypes=[("MP4","*.mp4")])
        if p: self.out_entry.delete(0,tk.END); self.out_entry.insert(0,p)
    def open_output_folder(self):
        path_str=self.out_entry.get().strip()
        if not path_str:
            messagebox.showerror("Відкрити папку","Спочатку вкажіть шлях до вихідного файлу."); return
        try: folder=Path(path_str).expanduser().resolve().parent
        except Exception as e:
            messagebox.showerror("Відкрити папку",f"Некоректний шлях: {e}"); return
        try: folder.mkdir(parents=True,exist_ok=True)
        except: pass
        try:
            if os.name=="nt": os.startfile(str(folder))
            elif sys.platform=="darwin": subprocess.Popen(["open",str(folder)])
            else: subprocess.Popen(["xdg-open",str(folder)])
        except Exception as e:
            messagebox.showerror("Відкрити папку",f"Не вдалося відкрити теку:\n{e}")
    def pick_audio(self):
        p=filedialog.askopenfilename(title="Вибери аудіо",
            filetypes=[("Audio","*.mp3 *.wav *.m4a *.aac *.flac *.ogg *.opus"),("Усі файли","*.*")])
        if p: self.audio_entry.delete(0,tk.END); self.audio_entry.insert(0,p)
    def clear_logs(self):
        self.log.delete("1.0",tk.END)
        with self.log_q.mutex: self.log_q.queue.clear()
        self.status.configure(text="Логи очищено")

    def toggle_video_params(self):
        if self.same_params.get()==1:
            if self.vidf.winfo_manager(): self.vidf.pack_forget()
        else:
            if not self.vidf.winfo_manager(): self.vidf.pack(before=self.mode_enc,fill=tk.X,pady=6)

    # ---------- Перевірка сумісності ----------
    def _probe_signature(self, path:str):
        try:
            out=subprocess.check_output(
                ["ffprobe","-v","error",
                 "-select_streams","v:0,a:0",
                 "-show_entries","stream=codec_type,codec_name,width,height,pix_fmt,avg_frame_rate,channels,sample_rate",
                 "-of","json", path], text=True)
            data=json.loads(out)
            vcodec=width=height=pix=fps=None; acodec=ch=sr=None
            for s in data.get("streams",[]):
                t=s.get("codec_type")
                if t=="video":
                    vcodec=s.get("codec_name"); width=s.get("width"); height=s.get("height"); pix=s.get("pix_fmt")
                    afr=s.get("avg_frame_rate") or "0/0"
                    if "/" in afr and afr!="0/0":
                        num,den=afr.split("/")
                        try: fps=round(float(num)/float(den),3)
                        except: fps=afr
                    else: fps=afr
                elif t=="audio":
                    acodec=s.get("codec_name"); ch=s.get("channels"); sr=s.get("sample_rate")
            return (vcodec,width,height,pix,fps,acodec,ch,sr)
        except Exception:
            return None

    def _compat_result(self, files):
        sig0=None; bad=[]
        for p in files:
            sig=self._probe_signature(p)
            if sig is None:
                bad.append(f"{Path(p).name}: не вдалося прочитати"); continue
            if sig0 is None: sig0=sig
            elif sig!=sig0:
                labels=["vcodec","width","height","pix_fmt","fps","acodec","channels","sample_rate"]
                dif=[f"{labels[i]}: {sig[i]} ≠ {sig0[i]}" for i in range(len(sig)) if sig[i]!=sig0[i]]
                bad.append(f"{Path(p).name}: "+("; ".join(dif) if dif else "відмінності"))
        return (not bad and sig0 is not None), ("\n".join(bad) if bad else "Немає даних")

    def check_and_recommend(self):
        files=[self.listbox.get(i) for i in range(self.listbox.size())]
        if not files: messagebox.showerror("Перевірка","Список порожній."); return
        ok, info = self._compat_result(files)
        if ok:
            self.same_params.set(1); self.toggle_video_params(); self.out_mode.set("copy")
            self.log_q.put("[ІНФО] Усі кліпи сумісні. Рекомендовано: «Склеїти як є».\n")
            messagebox.showinfo("Перевірка сумісності","✅ Усі кліпи однакові.\nРежим: «Склеїти як є».")
        else:
            self.same_params.set(0); self.toggle_video_params(); self.out_mode.set("norm")
            self.log_q.put("[ПОПЕРЕДЖЕННЯ] Кліпи відрізняються — рекомендую «Нормалізувати кожен».\n")
            messagebox.showwarning("Перевірка сумісності","❌ Є відмінності.\nРежим: «Нормалізувати кожен».\n\n"+info)

    # ---------- Побудова/фільтри/кодек ----------
    def build_concat(self, files, path:Path):
        with open(path,"w",encoding="utf-8") as f:
            for p in files: f.write(f"file '{Path(p).resolve().as_posix()}'\n")

    def video_filters_and_rate(self):
        if self.same_params.get()==1: return None,[]
        vf=[]; preset=self.res_preset.get()
        if preset!="Оригінал":
            w=preset.split("x")[0]; vf.append(f"scale={w}:-2")
        fps=self.fps_choice.get(); rate=[]
        if fps!="Оригінал":
            vf.append(f"fps={fps}"); rate=["-r",fps,"-vsync","cfr"]
        return (",".join(vf) if vf else None), rate

    def expand_to_duration(self, files, target_s):
        if not files: return []
        durs=[]
        for p in files:
            try:
                out=subprocess.check_output(
                    ["ffprobe","-v","error","-show_entries","format=duration",
                     "-of","default=nokey=1:noprint_wrappers=1",str(p)], text=True)
                durs.append(float(out.strip()))
            except Exception: durs.append(0.0)
        out=[]; tot=0.0; i=0
        if all(d<=0 for d in durs):
            while tot<target_s: out+=files; tot+=60
            return out
        while tot<target_s:
            out.append(files[i%len(files)]); tot+=durs[i%len(files)] or 1.0; i+=1
        return out

    def choose_encoder_args(self, vf, rate):
        want_copy=(self.quick_copy.get()==1) or (self.codec_choice.get()=="Без перекодування (copy)")
        if want_copy and not vf and not rate: return ["-c:v","copy"], True
        if want_copy and (vf or rate):
            self.log_q.put("[ПОВІДОМЛЕННЯ] Неможливо 'copy': змінюється роздільна або FPS.\n")
        c=self.codec_choice.get()
        if c=="NVENC (NVIDIA)": return ["-c:v","h264_nvenc","-preset","fast","-b:v","5M"], False
        if c=="QSV (Intel)":   return ["-c:v","h264_qsv","-preset","fast","-b:v","5M"], False
        if c=="AMF (AMD)":     return ["-c:v","h264_amf","-quality","speed","-b:v","5M"], False
        return ["-c:v","libx264","-preset","veryfast","-crf",str(int(self.crf.get()))], False

    # ---------- Процеси ----------
    def run_cmd(self, cmd):
        self.log_q.put("$ "+" ".join(cmd)+"\n")
        p=subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, bufsize=1)
        self.current_proc=p
        try:
            for line in p.stdout:  # type: ignore
                if self.stop_flag.is_set():
                    try: p.terminate()
                    except: pass
                    try: p.kill()
                    except: pass
                    self.log_q.put("[СТОП] Процес перервано користувачем.\n")
                    break
                self.log_q.put(line)
        finally:
            p.wait(); self.current_proc=None
        return p.returncode

    def on_stop(self):
        self.stop_flag.set()
        if self.current_proc is not None:
            try: self.current_proc.terminate()
            except: pass
            try: self.current_proc.kill()
            except: pass
        self.status.configure(text="Зупинено користувачем")

    # ---------- Старт ----------
    def start_clicked(self):
        try:
            self.log_q.put(">> START CLICK\n"); self.on_start()
        except Exception as e:
            self.log_q.put(f"[ПОМИЛКА on_start] {e}\n")
            self.set_running(False); self.worker=None; self.stop_flag.clear()

    def on_start(self):
        if self.worker and not self.worker.is_alive():
            self.worker=None; self.stop_flag.clear(); self.set_running(False)
        if self.running or (self.worker and self.worker.is_alive()):
            self.log_q.put("[ІНФО] Вже виконується — другий старт ігнорую.\n"); return
        if not have_ffmpeg():
            messagebox.showerror("FFmpeg","Не знайдено ffmpeg/ffprobe у PATH."); self.set_running(False); return

        files=[self.listbox.get(i) for i in range(self.listbox.size())]
        if not files:
            messagebox.showerror("Список порожній","Додай відео у список."); self.set_running(False); return

        target=parse_duration(self.dur_entry.get()) or 3600
        out_file=Path(self.out_entry.get()).expanduser().resolve(); out_file.parent.mkdir(parents=True,exist_ok=True)

        # Перша підготовка (порядок/аудіо/час)
        audio_path=self.audio_entry.get().strip()
        use_audio=len(audio_path)>0 and Path(audio_path).exists()
        audio_dur=ffprobe_duration(Path(audio_path)) if use_audio else 0.0
        fixed=self.fixed_duration.get()==1; trim=self.trim_to_audio.get()==1

        t_args=[]
        if not fixed and trim and audio_dur>0: t_args=["-t",str(int(audio_dur))]
        elif fixed and trim and audio_dur>0:    t_args=["-t",str(min(target,int(audio_dur)))]
        elif fixed:                              t_args=["-t",str(target)]
        add_shortest=(use_audio and trim and audio_dur>0)
        if use_audio and trim and audio_dur==0:
            self.log_q.put("[ПОПЕРЕДЖЕННЯ] Аудіо 0с/недоступне — ігнорую обрізання.\n")

        vf, rate = self.video_filters_and_rate()
        vcodec_args, is_copy = self.choose_encoder_args(vf, rate)

        self.stop_flag.clear(); self.set_running(True)

        def worker():
            try:
                total_jobs = int(self.batch_spin.get() or "1")
                if total_jobs < 1: total_jobs = 1
                base_files = list(files)

                for job_idx in range(1, total_jobs + 1):
                    if self.stop_flag.is_set(): raise RuntimeError("Зупинено")

                    self.log_q.put(f"\n=== Компіляція {job_idx}/{total_jobs} ===\n")

                    # Перемішування
                    if self.batch_shuffle.get() == 1:
                        if self.shuffle_mode.get()=="block":
                            bsz=self.block_size or infer_block_size(base_files)
                            job_files=shuffle_blockwise_no_seam(base_files, bsz)
                            job_files=enforce_no_adjacent_duplicates(job_files)
                        else:
                            job_files=shuffle_full(base_files)
                    else:
                        job_files=list(base_files)

                    # Автозаповнення
                    job_target=target
                    if self.autofill.get()==1:
                        fill=int(t_args[1]) if t_args else job_target
                        job_files=self.expand_to_duration(job_files, fill)

                    # Робочий каталог
                    out_file_n = self._numbered_out(out_file, job_idx) if total_jobs>1 else out_file
                    work=out_file_n.parent/"_vmix_work"; work.mkdir(exist_ok=True)
                    concat=work/"concat.txt"; self.build_concat(job_files, concat)

                    # Нормалізація (якщо обрано)
                    if self.out_mode.get()=="norm" and not is_copy:
                        norm=work/"_norm"; norm.mkdir(exist_ok=True)
                        for i,src in enumerate(job_files,1):
                            if self.stop_flag.is_set(): raise RuntimeError("Зупинено")
                            outp=norm/f"clip_{i:03d}.mp4"
                            if not outp.exists():
                                cmd=["ffmpeg","-y","-hide_banner","-loglevel","warning",
                                     "-fflags","+genpts","-avoid_negative_ts","make_zero","-i",src]
                                if vf: cmd+=["-vf",vf]
                                cmd+=rate
                                enc,_=self.choose_encoder_args(vf,rate); cmd+=enc
                                if enc[:2]==["-c:v","libx264"]:
                                    cmd+=["-g","60","-sc_threshold","0","-pix_fmt","yuv420p"]
                                else:
                                    cmd+=["-g","60","-pix_fmt","yuv420p"]
                                cmd+=["-c:a","aac","-b:a",self.abr.get(),"-ar","48000","-ac","2",
                                      "-movflags","+faststart", str(outp)]
                                rc=self.run_cmd(cmd)
                                if rc!=0 or self.stop_flag.is_set():
                                    raise RuntimeError("Зупинено або помилка нормалізації")
                        job_files_norm=[str((work/"_norm")/f"clip_{i:03d}.mp4") for i in range(1,len(job_files)+1)]
                        self.build_concat(job_files_norm, concat)

                    # Фінальна команда
                    cmd=["ffmpeg","-y","-hide_banner","-loglevel","warning",
                         "-fflags","+genpts","-avoid_negative_ts","make_zero",
                         "-f","concat","-safe","0","-i",str(concat)]
                    if use_audio: cmd+=["-i",audio_path]
                    if vf: cmd+=["-vf",vf]
                    cmd+=rate
                    if use_audio:
                        cmd+=["-map","0:v:0?","-map","1:a:0?"]
                    cmd+=vcodec_args
                    if not is_copy:
                        if vcodec_args[:2]==["-c:v","libx264"]:
                            cmd+=["-g","60","-sc_threshold","0","-pix_fmt","yuv420p"]
                        else:
                            cmd+=["-g","60","-pix_fmt","yuv420p"]
                    cmd+=["-c:a","aac","-b:a",self.abr.get(),"-ar","48000","-ac","2","-movflags","+faststart"]
                    cmd+=t_args
                    if add_shortest: cmd+=["-shortest"]
                    cmd+=[str(out_file_n)]

                    rc=self.run_cmd(cmd)

                    # Ретрай без -map
                    if rc!=0 and use_audio and not self.stop_flag.is_set():
                        self.log_q.put("[INFO] Повтор без явного -map (сумісність).\n")
                        cmd_nomap=[]; skip=False
                        for tok in cmd:
                            if skip: skip=False; continue
                            if tok=="-map": skip=True; continue
                            cmd_nomap.append(tok)
                        rc=self.run_cmd(cmd_nomap)

                    if self.stop_flag.is_set():
                        self.log_q.put("[СТОП] Перервано користувачем.\n")
                        break
                    elif rc!=0:
                        raise RuntimeError("Помилка фінального збирання")

                    self.log_q.put(f"ГОТОВО → {out_file_n}\n")

                    # чистимо робочу папку після кожної збірки
                    try:
                        if work.exists(): shutil.rmtree(work, ignore_errors=True)
                        self.log_q.put("[ІНФО] Тимчасова папка _vmix_work видалена.\n")
                    except Exception as e:
                        self.log_q.put(f"[ПОПЕРЕДЖЕННЯ] Не вдалося видалити _vmix_work: {e}\n")

                self.root.after(0, lambda: (messagebox.showinfo("Готово","Пакетна збірка виконана."),
                                            self.status.configure(text="Готово")))
            except Exception as e:
                if str(e)!="Зупинено":
                    self.log_q.put("[ПОМИЛКА] "+str(e)+"\n")
                    self.root.after(0, lambda: self.status.configure(text="Помилка"))
                    self.root.after(0, lambda: messagebox.showerror("Помилка", str(e)))
            finally:
                self.set_running(False); self.worker=None; self.stop_flag.clear()

        self.worker=threading.Thread(target=worker,daemon=True); self.worker.start()

# ---------- main ----------
if __name__=="__main__":
    root=tk.Tk()
    App(root)
    root.mainloop()
